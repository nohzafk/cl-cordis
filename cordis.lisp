;;; Cordis in Common Lisp: a live-image component meta-framework whose
;;; scheduling, cascading reload, hook chains, and reverse-undo decisions are
;;; taken by formally proved Bend 2 cores (bend/, pre-emitted in cores/).
;;;
;;; A component declares the keys it reads (inject) and the keys it provides,
;;; and has one function, its apply. A fiber is one loaded instance of a
;;; component. Everything a fiber does to the image goes through EFFECT, which
;;; keeps the inverse in the fiber's ledger.
;;;
;;; One operation runs at a time: load (USE), unload (RETIRE), a key the root
;;; sets, REBUILD, REVIVE, APPLY-CONFIG. After each, the cores decide what
;;; happens: cascade, which active fibers restart because a key they read
;;; changed (stopped newest first); plan, which fiber activates next (started
;;; one at a time, planned again after each); check, whether a load is refused;
;;; undo, the order a ledger's inverses run in; keys.missing, which provided key
;;; an activation left unset, and which needed key nothing declares.
;;;
;;; Interception, from the Cordis paper (3.2.3), which bendcord's Cordis does not
;;; have: a key may carry metadata beside its value. A component declares its
;;; own (its metadata), and each context it is in adds to it: every fiber from
;;; the root down carries what it was loaded with (its intercept), and
;;; WITH-INTERCEPT derives a context for the extent of a body. METADATA merges
;;; them by the key's rule (MERGE-RULE), the innermost last; the provider reads
;;; it when it is called. Metadata is no value: changing it reloads nothing.
;;;
;;; Hooks, bendcord's wrapper chains: the root declares a hook with its
;;; default (DEFINE-HOOK), a component wraps hooks (:wrap), and CHAIN runs the
;;; wrappers of the active fibers over the default, the first loaded outermost.
;;; The core cordis/hooks keeps the order and decides what a wrapper's INNER
;;; reaches.
;;;
;;; Where this differs from bendcord: an apply that signals an error is not
;;; rolled back at once. The operation parks where the error was signalled,
;;; with its stack; ABANDON, one of the restarts on offer, is bendcord's
;;; rollback. While it is parked, every other operation is refused at once.

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :sb-md5))

(defpackage #:cl-cordis
  (:nicknames #:cordis)
  (:use #:cl)
  (:shadow #:provide)
  (:export #:start #:stop #:running-p
           #:component #:make-component #:component-name #:component-inject #:component-provide
           #:use #:retire #:rebuild #:revive #:fibers #:find-fiber #:blocked
           #:watch #:changes #:status #:active #:faults
           #:fiber-id #:fiber-uid #:fiber-state #:fiber-error #:fiber-failures #:fiber-config #:fiber-parent
           #:settle #:await #:parked #:respond #:parked-report
           #:*fiber* #:in-fiber #:effect #:revertible #:provide #:inject #:value #:config #:thread
           #:eval-form #:bind-function #:load-text #:definition-source #:undo-definition #:definitions
           #:file-component #:apply-config #:amend-entry #:entries
           #:image #:image-lines #:image-diff
           #:cordis-error #:undeclared-access #:inactive-access #:provision-conflict #:not-root #:duplicate-id
           #:component-parked
           #:providing #:providers #:metadata #:merge-rule #:with-intercept #:fiber-intercept #:component-metadata
           #:define-hook #:chain #:chain-of #:component-wrap #:unknown-hook #:stale-inner #:stale-inner-reason
           #:abandon #:retry))

(in-package #:cl-cordis)

(define-condition cordis-error (error)
  ((message :initarg :message :reader cordis-error-message))
  (:report (lambda (c s) (write-string (cordis-error-message c) s))))
(define-condition undeclared-access (cordis-error) ())
(define-condition inactive-access (cordis-error) ())
(define-condition provision-conflict (cordis-error) ())
(define-condition not-root (cordis-error) ())
(define-condition duplicate-id (cordis-error) ())
(define-condition component-parked (cordis-error) ())
(define-condition unknown-hook (cordis-error) ())
(define-condition stale-inner (cordis-error)
  ((reason :initarg :reason :reader stale-inner-reason))
  (:documentation "A wrapper's INNER called outside its call: REASON is :ended, :stale or :unissued."))

(defun fail (type control &rest args)
  (error type :message (apply #'format nil control args)))

;;; ---- the cores ----
;;; The proved cores take Nats and lists of them. Each function here interns
;;; what it is given, asks one core, and maps the answer back: the decision is
;;; the core's. A comp is (thing inject provide); for check, thing is the id.

(defun interner ()
  (let ((table (make-hash-table :test 'equal)) (back (make-array 8 :adjustable t :fill-pointer 0)))
    (values (lambda (x)
              (or (gethash x table)
                  (progn (vector-push-extend x back)
                         (setf (gethash x table) (1- (fill-pointer back))))))
            (lambda (n) (aref back n)))))

(defun bend-comps (comps key id)
  "COMPS as the cores' Comp: the id is what ID gives for each comp and its position."
  (loop for c in comps for i from 0
        collect (cl-cordis.core.comp:make-comp (funcall id c i)
                                            (mapcar key (second c))
                                            (mapcar key (third c)))))

(defun core-check (root comps)
  "nil, (:dup-id id) or (:dup-key key): the first defect of COMPS over ROOT (core check)."
  (multiple-value-bind (key key-back) (interner)
    (multiple-value-bind (id id-back) (interner)
      (let ((r (cl-cordis.core.check:check (mapcar key root)
                                        (bend-comps comps key (lambda (c i) (declare (ignore i)) (funcall id (first c)))))))
        (when (cl-cordis.base:bend-some-p r)
          (let ((e (cl-cordis.base:bend-some-value r)))
            (if (cl-cordis.core.check:dupid-p e)
                (list :dup-id (funcall id-back (cl-cordis.core.check:dupid-id e)))
                (list :dup-key (funcall key-back (cl-cordis.core.check:dupkey-key e))))))))))

(defun core-plan (root comps)
  "The activation order over ROOT, and the comps left blocked (core plan): two lists of COMPS' things."
  (let ((key (interner)) (v (coerce comps 'vector)))
    (let ((p (cl-cordis.core.plan:plan (mapcar key root) (bend-comps comps key (lambda (c i) (declare (ignore c)) i)))))
      (flet ((back (l) (mapcar (lambda (c) (first (aref v (cl-cordis.core.comp:comp-id c)))) l)))
        (values (back (cl-cordis.core.plan:plan-order p)) (back (cl-cordis.core.plan:plan-blocked p)))))))

(defun core-cascade (order dirty)
  "The things of ORDER, an activation order of comps, that restart when the keys DIRTY change (core cascade)."
  (let ((key (interner)) (v (coerce order 'vector)))
    (mapcar (lambda (c) (first (aref v (cl-cordis.core.comp:comp-id c))))
            (cl-cordis.core.cascade:cascade (bend-comps order key (lambda (c i) (declare (ignore c)) i))
                                         (mapcar key dirty)))))

(defun core-undo (ledger)
  "The values of LEDGER, newest entry first, (:e value) or (:c value entries), in the order their inverses run (core undo)."
  (let ((v (make-array 8 :adjustable t :fill-pointer 0)))
    (labels ((conv (entries)
               (mapcar (lambda (e)
                         (let ((i (vector-push-extend (second e) v)))
                           (ecase (first e)
                             (:e (cl-cordis.core.undo:make-eff i))
                             (:c (cl-cordis.core.undo:make-sub i (conv (third e)))))))
                       entries)))
      (mapcar (lambda (i) (aref v i)) (cl-cordis.core.undo:undo (conv ledger))))))

(defun core-missing (names have)
  "The first of NAMES not in HAVE, or nil (core keys, missing)."
  (multiple-value-bind (key key-back) (interner)
    (let ((r (cl-cordis.core.keys:missing (mapcar key names) (mapcar key have))))
      (and (cl-cordis.base:bend-some-p r) (funcall key-back (cl-cordis.base:bend-some-value r))))))

;;; ---- the hook chains ----
;;; bendcord's HookChains (packages/cordis/src/core.ts) on the core cordis/hooks:
;;; the wrappers of every hook in the order they run, and the open calls of
;;; every activation. Every answer is the core's; this shell keeps the state and
;;; names fiber ids by number. A snapshot is the core's list of entries, a token
;;; the core's Token. A link is (:default) or (:plugin id).

(defstruct (chains (:constructor make-chains ()))
  (ids (make-hash-table :test 'equal))                  ; fiber id -> its number
  (names (make-array 8 :adjustable t :fill-pointer 0))  ; number -> fiber id
  (hooks (make-hash-table :test 'equal))                ; hook -> the core's entries
  (calls (make-hash-table :test 'equal))                ; fiber id -> the core's Calls of its activation
  (activations 0))

(defun chains-nat (c id)
  (or (gethash id (chains-ids c))
      (setf (gethash id (chains-ids c)) (vector-push-extend id (chains-names c)))))

(defun chains-of (c hook)
  (values (gethash hook (chains-hooks c) '())))

(defun chains-link (c link)
  (if (cl-cordis.core.hooks:owner-p link)
      (list :plugin (aref (chains-names c) (cl-cordis.core.hooks:owner-plugin link)))
      (list :default)))

(defun chains-add (c hook id)
  "Append ID's wrapper to HOOK's chain (core add); nil when ID has one there already."
  (let ((r (cl-cordis.core.hooks:add (chains-nat c id) (chains-of c hook))))
    (when (cl-cordis.base:bend-some-p r)
      (setf (gethash hook (chains-hooks c)) (cl-cordis.base:bend-some-value r))
      t)))

(defun chains-remove (c id)
  "Drop ID's wrapper from every hook, the others keeping their order (core remove)."
  (let ((n (chains-nat c id)))
    (loop for hook being the hash-keys of (chains-hooks c) using (hash-value es)
          do (setf (gethash hook (chains-hooks c)) (cl-cordis.core.hooks:bend-remove n es)))))

(defun chains-rejoin (c id hooks)
  "The chains once a new version of ID that wraps HOOKS stands in for the old
(core rejoin): on those hooks its wrapper keeps its place, or is appended; on any other it leaves."
  (let ((n (chains-nat c id)))
    (dolist (hook (union (loop for h being the hash-keys of (chains-hooks c) collect h) hooks :test #'equal))
      (setf (gethash hook (chains-hooks c))
            (cl-cordis.core.hooks:rejoin (and (member hook hooks :test #'equal) t) n (chains-of c hook))))))

(defun chains-snapshot (c hook active-p)
  "The chain a call of HOOK starting now runs: the wrappers of the ids ACTIVE-P holds for, in their order (core remove)."
  (let* ((all (chains-of c hook)) (snap all))
    (dolist (e all snap)
      (let ((n (cl-cordis.core.hooks:entry-plugin e)))
        (unless (funcall active-p (aref (chains-names c) n))
          (setf snap (cl-cordis.core.hooks:bend-remove n snap)))))))

(defun chains-step (c snap position)
  "The link at POSITION of SNAP (core step): the end of a chain is the default."
  (chains-link c (cl-cordis.core.hooks:bend-step snap position)))

(defun chains-activate (c id)
  "A fresh activation of ID, with no calls (core begin)."
  (setf (gethash id (chains-calls c))
        (cl-cordis.core.hooks:begin (prog1 (chains-activations c) (incf (chains-activations c))))))

(defun chains-admits (c id hooks &optional replacing)
  "Whether ID could append a wrapper for each of HOOKS, a hook named twice
counting twice (core add); REPLACING judges as if ID's own wrappers were gone."
  (let ((n (chains-nat c id)) (trial (make-hash-table :test 'equal)))
    (dolist (hook hooks t)
      (let ((r (cl-cordis.core.hooks:add n (multiple-value-bind (es has) (gethash hook trial)
                                          (cond (has es)
                                                (replacing (cl-cordis.core.hooks:bend-remove n (chains-of c hook)))
                                                (t (chains-of c hook)))))))
        (unless (cl-cordis.base:bend-some-p r) (return nil))
        (setf (gethash hook trial) (cl-cordis.base:bend-some-value r))))))

(defun chains-open (c id snap position)
  "Open a call of ID's activation on SNAP for its wrapper at POSITION: the token
of the rest of the chain (core issue), or nil when ID never activated."
  (let ((state (gethash id (chains-calls c))))
    (when state
      (let ((r (cl-cordis.core.hooks:issue position snap state)))
        (setf (gethash id (chains-calls c)) (cl-cordis.core.hooks:state-of r))
        (cl-cordis.core.hooks:token-of r)))))

(defun chains-resolve (c id token)
  "What TOKEN resolves to (core resolve): (:resolved link), (:unissued), (:ended)
or (:stale); nil when ID never activated."
  (let ((state (gethash id (chains-calls c))))
    (when state
      (let ((o (cl-cordis.core.hooks:resolve token state)))
        (cond ((cl-cordis.core.hooks:resolved-p o) (list :resolved (chains-link c (cl-cordis.core.hooks:resolved-link o))))
              ((cl-cordis.core.hooks:unissued-p o) (list :unissued))
              ((cl-cordis.core.hooks:ended-p o) (list :ended))
              (t (list :stale)))))))

(defun chains-end (c id token)
  "End the call TOKEN names (core finish): a token of another activation ends nothing."
  (let ((state (gethash id (chains-calls c))))
    (when state
      (setf (gethash id (chains-calls c)) (cl-cordis.core.hooks:finish token state)))))

;;; ---- the records ----

(defstruct component
  name
  (inject '())     ; the keys it reads
  (provide '())    ; the keys it must set before its apply returns
  apply            ; called with the fiber's config when the fiber activates; nil sets nothing
  fingerprint      ; what tells this component's code from another version of it
  (metadata '())   ; key value ...: what it declares of the keys it reads (METADATA)
  (wrap '()))      ; ((hook . wrapper) ...): the hooks it wraps, at most once each (CHAIN)

(defstruct (fiber (:print-object print-fiber))
  uid id component config parent
  (intercept '())  ; key value ...: the metadata the context it was loaded in adds (METADATA)
  (ledger '())     ; newest first: (:effect . dispose) or (:child . fiber)
  (committed '())  ; (key . binding): what it reads, fixed when it activates
  live             ; from the start of its activation until it is stopped
  active           ; once its apply has returned with every key it provides set
  retired          ; once it has left the loaded fibers
  error            ; why it failed: it stays out until REVIVE or REBUILD
  (failures '()))  ; the inverses that failed, as text

(defun fiber-state (fiber)
  "One of :active, :loading (activating, or parked there), :failed, :inactive."
  (cond ((fiber-error fiber) :failed)
        ((fiber-active fiber) :active)
        ((fiber-live fiber) :loading)
        (t :inactive)))

(defun print-fiber (fiber stream)
  (print-unreadable-object (fiber stream)
    (format stream "fiber ~a ~(~a~)" (fiber-id fiber) (fiber-state fiber))))

(defstruct binding key value fiber)

(defstruct layer fiber value source dispose)
(defstruct entry id print fiber)
(defstruct op fn started done values condition)

(defstruct runtime
  (lock (sb-thread:make-mutex :name "cordis"))
  (queue (sb-thread:make-waitqueue :name "cordis"))
  root
  (loaded '())                             ; the loaded fibers, in load order
  (live '())                               ; the live fibers, in activation order
  (store (make-hash-table :test 'equal))   ; key -> binding
  (root-keys '())                          ; the keys the root has set
  (dirty '())                              ; keys set since the last cascade
  (watchers '())                           ; (token . function), oldest first: called with a key at each write to it (WATCH)
  (faults '())                             ; (id . text), newest first: the inverses that failed (FAULTS)
  (ops '())                                ; operations waiting to run, oldest first
  runner                                   ; the task that runs operations, while there are any
  activating                               ; the fiber whose apply the runner is in
  (parks 0)                                ; how many times a task of the runtime has parked
  (places (make-hash-table :test 'equal))  ; (:function name) or (:variable name) -> (what it was . layers, newest first)
  (merges (make-hash-table :test 'equal))  ; key -> (merge . empty): how its metadata merges (MERGE-RULE)
  (hooks (make-hash-table :test 'equal))   ; hook -> its default (DEFINE-HOOK)
  (chains (make-chains))                   ; the wrappers of every hook, and the calls open on them
  (replacing '())                          ; ids APPLY-CONFIG is putting a new version of: their wrappers keep their places
  (uid 0)
  scope service
  (stop (sc:make-chan))
  (threads '())                            ; (fiber . scope) for every thread a component started
  (entries '()))

(defvar *runtime* nil "The running runtime, or nil.")
(defvar *fiber* nil "The fiber this thread acts for; nil is the root.")
(defvar *op* nil "True in the thread that runs the runtime's operations.")
(defvar *in-apply* nil "True while a component's apply runs: an error there parks the operation.")

(defmacro locked ((rt) &body body)
  `(sb-thread:with-recursive-lock ((runtime-lock ,rt)) ,@body))

(defmacro checked ((rt) &body body)
  "Evaluate BODY with the runtime's lock held. (REFUSE type control args...) in
BODY leaves it and signals the error after the lock is released: a thread that
parks at an error must not hold the lock."
  (let ((problem (gensym "PROBLEM")) (values (gensym "VALUES")) (block (gensym "CHECKED")))
    `(let ((,problem nil) (,values '()))
       (locked (,rt)
         (setf ,values
               (multiple-value-list
                (block ,block
                  (flet ((refuse (type control &rest args)
                           (setf ,problem (list* type control args))
                           (return-from ,block nil)))
                    (declare (ignorable #'refuse))
                    ,@body)))))
       (when ,problem (apply #'fail ,problem))
       (values-list ,values))))

(defun changed (rt)
  (locked (rt) (sb-thread:condition-broadcast (runtime-queue rt))))

(defun wait-until (rt test &key timeout)
  "Wait until TEST, called with the runtime's lock held, is true. Never called with the lock held."
  (sc:wait-on (runtime-lock rt) (runtime-queue rt) test :timeout timeout))

(defun runtime ()
  (or *runtime* (fail 'cordis-error "no cordis runtime is running; (cordis:start) starts one")))

(defun running-p () (and *runtime* t))

(defun here (rt) (or *fiber* (runtime-root rt)))
(defun root-p (rt fiber) (eq fiber (runtime-root rt)))

(defmacro in-fiber ((fiber) &body body)
  "Evaluate BODY as FIBER: its effects are recorded with FIBER's. Nil is the root."
  `(let ((*fiber* ,fiber)) ,@body))

(defun installed-p (rt fiber)
  (or (root-p rt fiber) (fiber-live fiber)))

(defun ancestors (fiber)
  (loop for f = (fiber-parent fiber) then (fiber-parent f)
        while f collect f))

(defun comp-of (fiber &optional (thing fiber))
  (let ((c (fiber-component fiber)))
    (list thing (component-inject c) (component-provide c))))

;;; ---- operations ----

(defun runner-parked-p (rt)
  (let ((runner (runtime-runner rt)))
    (and runner (eq (sc:task-state runner) :parked))))

(defun parked-id (rt)
  (let ((f (runtime-activating rt)))
    (if f (fiber-id f) "an operation of cordis")))

(defun run-ops (rt)
  "The runner: each queued operation alone, then the keys it made dirty settled, until none is left."
  (let ((*runtime* rt) (*op* t) (*fiber* nil)
        (sc:*on-park* (lambda (task) (declare (ignore task)) (locked (rt) (incf (runtime-parks rt)) (changed rt)))))
    (loop
      (let ((op (locked (rt)
                  (cond ((runtime-ops rt) (pop (runtime-ops rt)))
                        ((runtime-dirty rt) :settle)
                        (t (setf (runtime-runner rt) nil)
                           (changed rt)
                           nil)))))
        (unless op (return))
        (unless (eq op :settle)
          (locked (rt) (setf (op-started op) t))
          (block run
            ;; A refusal or a fault outside a component's apply goes back to the caller; one in an apply parks.
            (handler-bind ((error (lambda (c)
                                    (unless *in-apply*
                                      (setf (op-condition op) c)
                                      (return-from run)))))
              (setf (op-values op) (multiple-value-list (funcall (op-fn op)))))))
        (loop
          (let ((keys (locked (rt) (shiftf (runtime-dirty rt) '()))))
            (reconcile rt :keys keys)
            (unless (locked (rt) (runtime-dirty rt)) (return))))
        (unless (eq op :settle)
          (locked (rt)
            (setf (op-done op) t)
            (changed rt)))))))

(defun operate (rt fn)
  "Run FN as one operation of the runtime, after the ones queued before it, and
return its values once it is done, or parked. In the runner's own thread, FN is
called at once. While an operation is parked, it is refused."
  (if *op*
      (funcall fn)
      (let ((op (make-op :fn fn)))
        (locked (rt)
          (setf (runtime-ops rt) (append (runtime-ops rt) (list op)))
          (unless (runtime-runner rt)
            (setf (runtime-runner rt)
                  (sc:spawn (lambda () (run-ops rt)) :scope (runtime-scope rt) :restarts nil
                                                     :name "cordis operations"))))
        (wait-until rt (lambda () (or (op-done op) (runner-parked-p rt))))
        ;; an operation that has not begun when one is parked is refused: it leaves the queue
        (checked (rt)
          (unless (or (op-done op) (op-started op))
            (setf (runtime-ops rt) (remove op (runtime-ops rt)))
            (refuse 'component-parked "~a is parked; answer it first: (cordis:parked-report) says with what"
                    (parked-id rt))))
        (when (op-condition op) (error (op-condition op)))
        (values-list (op-values op)))))

;;; ---- the ledger ----

(defun note-failure (rt fiber e)
  (locked (rt)
    (let ((text (princ-to-string e)))
      (push text (fiber-failures fiber))
      (push (cons (fiber-id fiber) text) (runtime-faults rt)))))

(defun wrote (rt key)
  "KEY was written: set, or cleared when what provides it stopped. Tell the watchers, oldest first, inside the write."
  (locked (rt)
    (dolist (w (runtime-watchers rt)) (funcall (cdr w) key))))

(defun drop-bindings (rt fiber)
  (locked (rt)
    (loop for b being the hash-values of (runtime-store rt)
          when (eq (binding-fiber b) fiber) do (remhash (binding-key b) (runtime-store rt)))))

(defun leave (rt fiber)
  "FIBER leaves the loaded fibers for good."
  (drop-bindings rt fiber)
  (locked (rt)
    (setf (fiber-committed fiber) '()
          (fiber-live fiber) nil
          (fiber-active fiber) nil
          (fiber-retired fiber) t
          (runtime-loaded rt) (remove fiber (runtime-loaded rt))
          (runtime-live rt) (remove fiber (runtime-live rt)))
    (unless (member (fiber-id fiber) (runtime-replacing rt) :test #'equal)
      (chains-remove (runtime-chains rt) (fiber-id fiber)))
    (let ((parent (fiber-parent fiber)))
      (when parent
        (setf (fiber-ledger parent) (remove fiber (fiber-ledger parent) :key #'cdr))))
    (changed rt)))

(defun take-ledger (rt fiber)
  "Take FIBER's ledger as the core's entries: its children's ledgers are taken
with it, and each child stops here. The entries, and the inverses by value."
  (let ((thunks '()))
    (labels ((take (fiber)
               (mapcar (lambda (entry)
                         (let ((n (length thunks)))
                           (ecase (car entry)
                             (:effect
                              (push (cons fiber (cdr entry)) thunks)
                              (list :e n))
                             (:child
                              (let ((child (cdr entry)))
                                (push (cons child (lambda () (leave rt child))) thunks)
                                (locked (rt)
                                  (setf (fiber-live child) nil
                                        (fiber-active child) nil
                                        (runtime-live rt) (remove child (runtime-live rt))))
                                (list :c n (take child)))))))
                       (locked (rt) (shiftf (fiber-ledger fiber) '())))))
      (let ((entries (take fiber)))
        (values entries (coerce (reverse thunks) 'vector))))))

(defun undo-ledger (rt fiber)
  "Run FIBER's inverses, and its children's, in the order the core undo gives. One that fails is recorded, and the rest still run."
  (multiple-value-bind (entries thunks) (take-ledger rt fiber)
    (dolist (n (core-undo entries))
      (destructuring-bind (owner . thunk) (aref thunks n)
        ;; an inverse runs as the fiber it belongs to, so that it reads what that fiber read
        (handler-case (let ((*fiber* owner)) (funcall thunk))
          (error (e) (note-failure rt owner e)))))))

(defun stop-fiber (rt fiber)
  "Stop FIBER: it is no longer live, its inverses run, and what it provided is cleared."
  (locked (rt)
    (setf (fiber-live fiber) nil
          (fiber-active fiber) nil
          (runtime-live rt) (remove fiber (runtime-live rt))))
  (undo-ledger rt fiber)
  (drop-bindings rt fiber)
  ;; every key it declares is cleared, one it never set too
  (dolist (key (component-provide (fiber-component fiber))) (wrote rt key))
  ;; what the fiber read stays readable until its last inverse has run
  (locked (rt)
    (setf (fiber-committed fiber) '())
    (changed rt)))

;;; ---- effects ----

(defun effect (callback)
  "Call CALLBACK, which changes something and returns the function that undoes
the change. The undo is kept in the ledger of the fiber this thread acts for,
and is run when that fiber stops. Returns a function that undoes it now, once."
  (let* ((rt (runtime)) (fiber (here rt)))
    (unless (locked (rt) (installed-p rt fiber))
      (fail 'cordis-error "~a is not installed: the effect would belong to nothing that can undo it" (fiber-id fiber)))
    (let ((inverse (funcall callback)))
      (when (functionp inverse)
        (let ((armed t) (dispose nil))
          (setf dispose
                (lambda ()
                  (when (locked (rt)
                          (prog1 armed
                            (setf armed nil
                                  (fiber-ledger fiber) (remove dispose (fiber-ledger fiber) :key #'cdr))))
                    (funcall inverse)
                    t)))
          (unless (locked (rt) (when (installed-p rt fiber) (push (cons :effect dispose) (fiber-ledger fiber)) t))
            ;; the fiber stopped while the callback ran
            (funcall dispose)
            (fail 'cordis-error "~a stopped while an effect of it ran; the effect is undone" (fiber-id fiber)))
          dispose)))))

(defmacro revertible (action &body undo)
  "Evaluate ACTION as an effect whose inverse is UNDO."
  `(effect (lambda () ,action (lambda () ,@undo))))

;;; ---- keys ----

(defun live-binding (rt key)
  "The binding at KEY when the root set it, or the fiber that set it is active."
  (let ((b (gethash key (runtime-store rt))))
    (and b (or (root-p rt (binding-fiber b)) (fiber-active (binding-fiber b))) b)))

(defun declarer (rt key)
  "Who declares KEY: :root, a loaded fiber, or nil."
  (if (member key (runtime-root-keys rt) :test #'equal)
      :root
      (find-if (lambda (f) (member key (component-provide (fiber-component f)) :test #'equal))
               (runtime-loaded rt))))

(defun root-set (rt key value)
  "The root sets KEY: only a key the runtime was started with is the root's to set."
  (checked (rt)
    (unless (member key (runtime-root-keys rt) :test #'equal)
      (refuse 'not-root "~s is not a root key: the root sets only the keys (cordis:start :root ...) names" key))
    (setf (gethash key (runtime-store rt)) (make-binding :key key :value value :fiber (runtime-root rt)))
    (wrote rt key)
    (pushnew key (runtime-dirty rt) :test #'equal)))

(defun provide (key value)
  "Set KEY to VALUE. A component sets only keys it declares, and must set each
before its apply returns; set again once it is active, the fibers that read the
key restart. The root sets only the keys the runtime was started with. Returns VALUE."
  (let* ((rt (runtime)) (fiber (here rt)))
    (if (root-p rt fiber)
        (operate rt (lambda () (root-set rt key value)))
        (let ((active
                (checked (rt)
                  (unless (member key (component-provide (fiber-component fiber)) :test #'equal)
                    (refuse 'undeclared-access "~a provides ~s without declaring it" (fiber-id fiber) key))
                  (unless (fiber-live fiber)
                    (refuse 'inactive-access "~a sets ~s while it is not installed" (fiber-id fiber) key))
                  (setf (gethash key (runtime-store rt)) (make-binding :key key :value value :fiber fiber))
                  (wrote rt key)
                  ;; while it activates, nothing that reads the key has started: nothing restarts
                  (when (fiber-active fiber)
                    (pushnew key (runtime-dirty rt) :test #'equal)
                    t))))
          ;; outside an operation, the consumers are settled before this returns, unless one is parked
          (when (and active (not *op*))
            (handler-case (operate rt (lambda () nil))
              (component-parked () nil)))))
    value))

(defun value (key)
  "The value at KEY, when the root set it or an active fiber did, and whether there is one. Never fails."
  (let* ((rt (runtime)) (b (locked (rt) (live-binding rt key))))
    (if b (values (binding-value b) t) (values nil nil))))

(defun inject (key)
  "The value at KEY as the fiber this thread acts for read it when it activated.
A component that a component instantiated also reads what its parent reads."
  (let ((rt (runtime)))
    (checked (rt)
      (loop for fiber = (here rt) then (fiber-parent fiber)
            do (when (or (null fiber) (root-p rt fiber))

                 (refuse 'undeclared-access "~a reads ~s, which it does not declare" (fiber-id (here rt)) key))
               (let ((cell (assoc key (fiber-committed fiber) :test #'equal)))
                 (when (and cell (cdr cell)) (return (binding-value (cdr cell)))))
               (when (member key (component-inject (fiber-component fiber)) :test #'equal)
                 (refuse 'inactive-access "~a reads ~s while it is not installed" (fiber-id fiber) key))))))

(defun providers (prefix)
  "The keys whose name is a string starting with PREFIX, with what they hold
now and who provides them, as (id key . value): the root's first, in the order
it set them, their id nil, then those of each active fiber, in the order the
fibers activated."
  (let ((rt (runtime)) (n (length prefix)))
    (flet ((hit (key) (and (stringp key) (>= (length key) n) (string= prefix key :end2 n))))
      (locked (rt)
        (append
         (loop for key in (runtime-root-keys rt)
               for b = (live-binding rt key)
               when (and b (hit key)) collect (list* nil key (binding-value b)))
         (loop for f in (runtime-live rt)
               when (fiber-active f)
                 append (loop for key in (component-provide (fiber-component f))
                              for b = (gethash key (runtime-store rt))
                              when (and (hit key) b (eq (binding-fiber b) f))
                                collect (list* (fiber-id f) key (binding-value b)))))))))

(defun providing (prefix)
  "The keys whose name is a string starting with PREFIX, with what they hold
now, as (key . value), in the order of PROVIDERS."
  (mapcar #'cdr (providers prefix)))

;;; ---- interception ----

(defvar *intercepts* '()
  "The metadata the contexts WITH-INTERCEPT derived add in this thread, the outermost first, each key value ...")

(defun merge-rule (key merge &optional empty)
  "Have KEY's metadata merged by MERGE, a function of two values that is
associative and has EMPTY as its identity; where the two disagree, the second
should win. A key without a rule keeps the later value. The rule is an effect
of the fiber this thread acts for, and leaves with it; a key has one rule."
  (let ((rt (runtime)) (taken nil))
    (effect (lambda ()
              (locked (rt)
                (if (gethash key (runtime-merges rt))
                    (setf taken t)
                    (setf (gethash key (runtime-merges rt)) (cons merge empty))))
              (unless taken
                (lambda () (locked (rt) (remhash key (runtime-merges rt)))))))
    (when taken (fail 'provision-conflict "~s has a merge rule already" key))
    key))

(defun property (plist key)
  (loop for (k v) on plist by #'cddr
        when (equal k key) do (return (values v t))))

(defun metadata (key)
  "KEY's metadata as the fiber this thread acts for reads it: what its component
declares, merged with what each context it is in adds, the outermost first:
every fiber from the root down to this one, then each WITH-INTERCEPT this
thread is in. Each is merged by KEY's rule (MERGE-RULE). Never fails."
  (let* ((rt (runtime))
         (fiber (locked (rt) (here rt)))
         (rule (locked (rt) (gethash key (runtime-merges rt))))
         (merge (if rule (car rule) (lambda (a b) (declare (ignore a)) b)))
         (acc (and rule (cdr rule))))
    (flet ((add (plist)
             (multiple-value-bind (v hit) (property plist key)
               (when hit (setf acc (funcall merge acc v))))))
      (unless (root-p rt fiber)
        (add (component-metadata (fiber-component fiber))))
      (dolist (f (reverse (cons fiber (ancestors fiber))))
        (unless (root-p rt f) (add (fiber-intercept f))))
      (dolist (layer *intercepts*) (add layer)))
    acc))

(defmacro with-intercept ((&rest keys-and-values) &body body)
  "Evaluate BODY in a context derived from this thread's, which adds the metadata
KEY VALUE ... (METADATA). Nothing in the runtime changes and nothing reloads;
the context ends with BODY, and threads started in BODY are not in it."
  `(call-with-intercept (list ,@keys-and-values) (lambda () ,@body)))

(defun call-with-intercept (layer fn)
  "Call FN in a context derived from this thread's, which adds LAYER, key value ... (WITH-INTERCEPT)."
  (let ((*intercepts* (append *intercepts* (list layer))))
    (funcall fn)))

(defun config (&optional (key nil key-p))
  "The config of the fiber this thread acts for; with KEY, that property of it."
  (let ((config (fiber-config (here (runtime)))))
    (if key-p (getf config key) config)))

;;; ---- the lifecycle ----

(defun activate (rt fiber)
  "Activate FIBER: commit what its keys hold, call its component's apply, and
check that it set every key it provides (core keys, missing). An error parks
the operation there; ABANDON undoes what the apply did and leaves the fiber
failed, RETRY undoes it and calls the apply again."
  (let ((component (fiber-component fiber)))
    (locked (rt)
      (setf (fiber-live fiber) t
            (fiber-active fiber) nil
            (runtime-live rt) (append (runtime-live rt) (list fiber))
            (runtime-activating rt) fiber)
      (chains-activate (runtime-chains rt) (fiber-id fiber))
      (changed rt))
    (flet ((commit ()
             (locked (rt)
               (setf (fiber-committed fiber)
                     (loop for key in (component-inject component)
                           collect (cons key (gethash key (runtime-store rt))))))))
      (commit)
      (let ((outcome
              (let ((*fiber* fiber) (*in-apply* t))
                (loop
                  (restart-case
                      (progn
                        (when (component-apply component)
                          (funcall (component-apply component) (fiber-config fiber)))
                        (let ((unset (core-missing (component-provide component)
                                                   (locked (rt)
                                                     (loop for key in (component-provide component)
                                                           for b = (gethash key (runtime-store rt))
                                                           when (and b (eq (binding-fiber b) fiber)) collect key)))))
                          (when unset
                            (fail 'cordis-error "~a returned without setting ~s, which it provides" (fiber-id fiber) unset)))
                        (return :done))
                    (retry ()
                      :report "Undo what the component has done so far, and call its apply again from the start."
                      (undo-ledger rt fiber)
                      (drop-bindings rt fiber)
                      (commit))
                    (abandon ()
                      :report "Undo what the component has done, and leave it failed."
                      (return :abandoned)))))))
        (let ((why (and (eq outcome :abandoned)
                        (or (let ((runner (runtime-runner rt))) (and runner (sc:task-condition runner)))
                            "abandoned"))))
          (locked (rt) (setf (runtime-activating rt) nil))
          (cond ((eq outcome :done)
                 (locked (rt)
                   (setf (fiber-active fiber) t)
                   (changed rt)))
                (t
                 (locked (rt) (setf (fiber-error fiber) why))
                 (stop-fiber rt fiber))))))))

(defun cascade-set (rt live keys leaving)
  "The fibers that stop: those the core cascade restarts for KEYS, LEAVING, and
the descendants of all of them, with the keys they provide dirty in turn."
  (let ((stop '()))
    (loop
      (let* ((keys (union keys (loop for f in leaving append (component-provide (fiber-component f))) :test #'equal))
             (set (union (core-cascade (mapcar #'comp-of live) keys) leaving))
             (kids (remove-if-not (lambda (f) (intersection (ancestors f) set)) (locked (rt) (runtime-loaded rt))))
             (next (union set kids)))
        (when (subsetp next stop) (return stop))
        (setf stop (union stop next)
              leaving (union leaving kids))))))

(defun next-to-activate (rt)
  "The first fiber of the core plan's order that is not live, or nil."
  (locked (rt)
    (let ((candidates (remove-if #'fiber-error (runtime-loaded rt))))
      (find-if-not #'fiber-live (core-plan (runtime-root-keys rt) (mapcar #'comp-of candidates))))))

(defun reconcile (rt &key keys removed failing restart)
  "Stop what KEYS reach and REMOVED, FAILING and RESTART, newest first; REMOVED
leave; then activate what the plan allows, one at a time, planning again after each."
  (let* ((live (locked (rt) (copy-list (runtime-live rt))))
         (stop (cascade-set rt live keys (union removed (union failing restart)))))
    (dolist (f (reverse live))
      (when (and (member f stop) (not (intersection (ancestors f) stop)) (fiber-live f))
        (stop-fiber rt f)))
    (dolist (f removed)
      (unless (fiber-retired f) (leave rt f)))
    (loop
      (let ((next (next-to-activate rt)))
        (unless next (return))
        (activate rt next)))))

(defun use (component &key config id intercept)
  "Load COMPONENT as a fiber under the fiber this thread acts for: it is one of
that fiber's effects, and leaves with it. It activates once every key it reads
is set. An id or a key another loaded fiber holds is refused (core check).
INTERCEPT, key value ..., is the metadata its context adds (METADATA); the
fibers under it inherit it. Returns the fiber when the operation is done, or parked."
  (let* ((rt (runtime)) (parent (here rt)) (id (or id (component-name component))))
    (operate rt
             (lambda ()
               (checked (rt)
                 (unless (installed-p rt parent)
                   (refuse 'cordis-error "~a is not installed: ~a would belong to nothing that can take it out" (fiber-id parent) id))
                 (let ((err (core-check (runtime-root-keys rt)
                                        (append (mapcar (lambda (f) (comp-of f (fiber-id f))) (runtime-loaded rt))
                                                (list (list id (component-inject component) (component-provide component)))))))
                   (case (first err)
                     (:dup-id (refuse 'duplicate-id "~a is loaded already" id))
                     (:dup-key (refuse 'provision-conflict "~a declares ~s, which ~a provides already" id (second err)
                                       (let ((d (declarer rt (second err)))) (if (fiber-p d) (fiber-id d) "the root"))))))
                 (let ((hooks (mapcar #'car (component-wrap component)))
                       (replacing (and (member id (runtime-replacing rt) :test #'equal) t)))
                   (let ((unknown (core-missing hooks (loop for h being the hash-keys of (runtime-hooks rt) collect h))))
                     (when unknown (refuse 'unknown-hook "~a wraps ~s, which is no hook" id unknown)))
                   (unless (chains-admits (runtime-chains rt) id hooks replacing)
                     (refuse 'cordis-error "~a wraps a hook twice" id))
                   (if replacing
                       (chains-rejoin (runtime-chains rt) id hooks)
                       (dolist (hook hooks) (chains-add (runtime-chains rt) hook id))))
                 (let ((fiber (make-fiber :uid (incf (runtime-uid rt)) :id id :component component
                                          :config config :parent parent :intercept intercept)))
                   (setf (runtime-loaded rt) (append (runtime-loaded rt) (list fiber)))
                   (push (cons :child fiber) (fiber-ledger parent))
                   (changed rt)
                   fiber))))))

(defun retire (fiber)
  "Take FIBER out for good: what reads what it provides stops first, then its
inverses run, its children's with them. Returns when it is out."
  (let ((rt (runtime)))
    (when (and *op* (eq fiber (runtime-activating rt)))
      (fail 'cordis-error "~a cannot be taken out from its own apply" (fiber-id fiber)))
    (operate rt (lambda () (unless (fiber-retired fiber) (reconcile rt :removed (list fiber)))))
    fiber))

(defun rebuild (fiber)
  "Stop FIBER and activate it again from the start, what reads it first. A
failed fiber is let in again. Returns when it is active again, parked, or waiting for a key."
  (let ((rt (runtime)))
    (when (eq *fiber* fiber)
      (fail 'cordis-error "~a cannot be rebuilt from its own apply" (fiber-id fiber)))
    (operate rt (lambda ()
                  (locked (rt) (setf (fiber-error fiber) nil (fiber-failures fiber) '()))
                  (reconcile rt :restart (and (fiber-live fiber) (list fiber)))))
    fiber))

(defun revive (fiber)
  "Let a failed FIBER activate again. Returns when the operation is done, or parked."
  (let ((rt (runtime)))
    (operate rt (lambda ()
                  (locked (rt) (setf (fiber-error fiber) nil (fiber-failures fiber) '()))))
    fiber))

(defun fibers ()
  "Every loaded fiber, in load order."
  (let ((rt (runtime))) (locked (rt) (copy-list (runtime-loaded rt)))))

(defun find-fiber (id)
  (find id (fibers) :key #'fiber-id :test #'equal))

;;; ---- observing: bendcord's watch, changes, status, active, faults ----

(defun watch (listener)
  "Call LISTENER with a key after each write to it: a set, or the clear when what
provides it stops. It runs inside the write, so it must return at once. Returns
the function that removes it; a listener added twice is called twice until each
registration is removed."
  (let ((rt (runtime)) (own (cons nil listener)))
    (locked (rt) (setf (runtime-watchers rt) (append (runtime-watchers rt) (list own))))
    (lambda ()
      (locked (rt) (setf (runtime-watchers rt) (remove own (runtime-watchers rt) :test #'eq)))
      nil)))

(defun changes (key listener)
  "Call LISTENER with what KEY holds and whether it holds anything: now, and after
each write to KEY. What a component set while it activates counts, as the write
it is. Returns the function that ends it."
  (let ((rt (runtime)))
    (flet ((tell ()
             (multiple-value-bind (b present) (gethash key (runtime-store rt))
               (funcall listener (and present (binding-value b)) present))))
      (locked (rt)
        (tell)
        (watch (lambda (name) (when (equal name key) (tell))))))))

(defun status (id)
  "How the component loaded as ID stands: nil when none is; :active; :failed and,
as a second value, why; else :blocked, which it also is while it activates."
  (let ((rt (runtime)))
    (locked (rt)
      (let ((fiber (find id (runtime-loaded rt) :key #'fiber-id :test #'equal)))
        (cond ((null fiber) nil)
              ((fiber-error fiber) (values :failed (fiber-error fiber)))
              ((fiber-active fiber) :active)
              (t :blocked))))))

(defun active ()
  "The ids of the active components, in activation order."
  (let ((rt (runtime)))
    (locked (rt)
      (loop for fiber in (runtime-live rt)
            when (and (fiber-active fiber) (not (root-p rt fiber))) collect (fiber-id fiber)))))

(defun faults ()
  "Every inverse that failed while its component stopped, as (id . text), oldest
first. The other inverses still ran."
  (let ((rt (runtime))) (locked (rt) (reverse (runtime-faults rt)))))

(defun idle-p (rt)
  (or (and (null (runtime-ops rt)) (null (runtime-runner rt)))
      (runner-parked-p rt)))

(defun settle (&key (timeout 30))
  "Wait until no operation runs or waits, or the one that runs is parked. Nil when TIMEOUT seconds pass first."
  (let ((rt (runtime)))
    (and (wait-until rt (lambda () (idle-p rt)) :timeout timeout) t)))

(defun await (fiber &key (timeout 30))
  "Settle, then FIBER's state; nil when TIMEOUT seconds pass first."
  (and (settle :timeout timeout) (fiber-state fiber)))

(defun blocked ()
  "The loaded fibers that are not live, each with why: (id :failed text); (id
:missing key) when nothing declares a key it reads (core keys, missing); (id
:cycle) when what it waits for waits for it; (id :waits key id) otherwise. The
fibers that wait are those the core plan leaves blocked."
  (let ((rt (runtime)))
    (locked (rt)
      (let* ((loaded (runtime-loaded rt))
             (stuck (nth-value 1 (core-plan (runtime-root-keys rt) (mapcar #'comp-of (remove-if #'fiber-error loaded)))))
             (declared (append (runtime-root-keys rt)
                               (loop for f in loaded append (component-provide (fiber-component f))))))
        (labels ((waits-for (fiber)
                   (loop for key in (component-inject (fiber-component fiber))
                         for d = (declarer rt key)
                         when (and (fiber-p d) (not (fiber-active d))) collect (cons key d)))
                 (reaches (from to seen)

                   (loop for (nil . d) in (waits-for from)
                         thereis (or (eq d to)
                                     (and (not (member d seen)) (reaches d to (cons d seen)))))))
          (loop for fiber in loaded
                for missing = (core-missing (component-inject (fiber-component fiber)) declared)
                when (fiber-error fiber)
                  collect (list (fiber-id fiber) :failed (princ-to-string (fiber-error fiber)))
                else when (member fiber stuck)
                  collect (let ((waits (waits-for fiber)))
                            (cond (missing (list (fiber-id fiber) :missing missing))
                                  ((reaches fiber fiber (list fiber)) (list (fiber-id fiber) :cycle))
                                  (waits (list (fiber-id fiber) :waits (car (first waits)) (fiber-id (cdr (first waits)))))
                                  (t (list (fiber-id fiber) :waits nil nil))))))))))

;;; ---- a parked operation ----

(defun parked ()
  "Every parked task of the runtime with its fiber, as (fiber . task): the operation first, then components' threads."
  (let ((rt (runtime)) (out '()))
    (locked (rt)
      (when (runner-parked-p rt)
        (push (cons (or (runtime-activating rt) (runtime-root rt)) (runtime-runner rt)) out))
      (loop for (fiber . scope) in (runtime-threads rt)
            do (dolist (task (sc:parked scope)) (push (cons fiber task) out))))
    (nreverse out)))

(defun parked-report ()
  "The parked tasks as plists: :id, :error, :restarts, :stack."
  (loop for (fiber . task) in (parked)
        collect (list :id (fiber-id fiber)
                      :error (princ-to-string (sc:task-condition task))
                      :restarts (sc:task-restarts task)
                      :stack (sc:task-report task))))

(defun respond (fiber restart &rest args)
  "Answer the parked task of FIBER, a fiber or an id, with RESTART and ARGS."
  (let ((cell (find-if (lambda (c) (or (eq (car c) fiber) (equal (fiber-id (car c)) fiber))) (parked))))
    (unless cell (fail 'cordis-error "~a has no parked task" (if (fiber-p fiber) (fiber-id fiber) fiber)))
    (unless (member restart (sc:task-restarts (cdr cell)))
      (fail 'cordis-error "~a offers no restart ~a; on offer: ~{~a~^, ~}" (fiber-id (car cell)) restart
            (sc:task-restarts (cdr cell))))
    (answer-and-wait (runtime) (cdr cell) restart args)
    (car cell)))

(defun answer-and-wait (rt task restart args)
  "Answer the parked TASK, and return once it has taken the answer: it runs, has ended, or has parked again."
  (let ((parks (locked (rt) (runtime-parks rt))))
    (apply #'sc:answer task restart args)
    (loop repeat 5000
          until (or (not (eq (sc:task-state task) :parked)) (> (locked (rt) (runtime-parks rt)) parks))
          do (sleep 0.001))))

;;; ---- a thread as an effect ----

(defun thread (fn &key (name "component thread"))
  "Start FN in a thread that acts for this fiber. Unloading the fiber cancels the thread where it waits, and waits for it to end."
  (let* ((rt (runtime)) (fiber (here rt)))
    (effect
     (lambda ()
       (let* ((ready (sc:make-chan))
              (supervisor
                (sc:spawn
                 (lambda ()
                   (handler-case
                       (sc:with-scope (scope :name name :on-failure :park)
                         (let ((*fiber* fiber) (*runtime* rt))
                           (let ((sc:*inherit* (list* '*fiber* '*runtime* sc:*inherit*)))
                             (sc:spawn fn :name name)))
                         (sc:send ready scope))
                     (sc:task-error () nil)))
                 :scope (runtime-scope rt) :restarts nil :name (format nil "~a, kept" name)))
              (scope (sc:recv ready :timeout 10)))
         (unless scope (fail 'cordis-error "the thread ~a did not start" name))
         (locked (rt) (push (cons fiber scope) (runtime-threads rt)))
         (lambda ()
           (sc:cancel-scope scope :unloaded)
           (sb-thread:join-thread (sc:task-thread supervisor) :default nil)
           (locked (rt) (setf (runtime-threads rt) (delete scope (runtime-threads rt) :key #'cdr)))))))))

;;; ---- definitions as effects ----
;;; A function, macro or variable a fiber defines is a layer on that name. The
;;; newest layer is what the name means; taking a layer out, wherever it lies,
;;; leaves the newest of the rest, and with none left what the name was before
;;; the first. So two fibers that define one name can leave in either order.

(defun place-value (place)
  (destructuring-bind (kind name) place
    (ecase kind
      (:function (cond ((macro-function name) (cons :macro (macro-function name)))
                       ((and (fboundp name) (not (special-operator-p name))) (cons :function (fdefinition name)))))
      (:variable (and (boundp name) (list :value (symbol-value name)))))))

(defun restore-place (place was)
  (destructuring-bind (kind name) place
    (ecase kind
      (:function (cond ((null was) (when (fboundp name) (fmakunbound name)))
                       ((eq (car was) :macro) (setf (macro-function name) (cdr was)))
                       (t (when (macro-function name) (fmakunbound name))
                          (setf (fdefinition name) (cdr was)))))
      (:variable (if was (setf (symbol-value name) (second was)) (makunbound name))))))

(defun remove-layer (rt place layer)
  (locked (rt)
    (let ((cell (gethash place (runtime-places rt))))
      (when (and cell (member layer (cdr cell)))
        (let ((top-p (eq layer (second cell))))
          (setf (cdr cell) (delete layer (cdr cell)))
          (when top-p
            (restore-place place (if (cdr cell) (layer-value (second cell)) (car cell))))
          (unless (cdr cell) (remhash place (runtime-places rt))))))))

(defun define-place (place thunk source)
  "Call THUNK, which defines PLACE, as an effect of this fiber; its values."
  (values-list (define-layer place thunk source)))

(defun define-layer (place thunk source)
  "Call THUNK, which defines PLACE, as an effect of this fiber: the list of its
values, and the layer. A function a
fiber defines again is one more layer, so that each can be undone; a variable a
fiber sets again changes the layer the fiber has, so that no earlier value is kept."
  (let* ((rt (runtime)) (fiber (here rt)) (results '()) (layer nil)
         (top (locked (rt) (second (gethash place (runtime-places rt))))))
    (flet ((run ()
             (setf results (multiple-value-list
                            (handler-bind ((sb-kernel:redefinition-warning #'muffle-warning))
                              (funcall thunk))))))
      (cond ((and top (eq (first place) :variable) (eq (layer-fiber top) fiber))
             (run)
             (locked (rt) (setf (layer-value top) (place-value place)
                                (layer-source top) source))
             (setf layer top))
            (t
             (let ((dispose
                     (effect
                      (lambda ()
                        (let ((before (place-value place)))
                          (run)
                          (setf layer (make-layer :fiber fiber :value (place-value place) :source source))
                          (locked (rt)
                            (let ((cell (or (gethash place (runtime-places rt))
                                            (setf (gethash place (runtime-places rt)) (list before)))))
                              (push layer (cdr cell))))
                          (lambda () (remove-layer rt place layer)))))))
               (setf (layer-dispose layer) dispose)))))
    (values results layer)))

(defun bind-function (name function &optional source)
  "Make FUNCTION the definition of the symbol NAME as an effect of this fiber: a
layer on NAME, as a DEFUN through EVAL-FORM is. Returns the function that takes
it out."
  (layer-dispose (nth-value 1 (define-layer (list :function name)
                                            (lambda () (setf (fdefinition name) function))
                                            source))))

(defun eval-form (form &optional source)
  "Evaluate FORM for this fiber. A top-level DEFUN, DEFMACRO, DEFPARAMETER or
DEFVAR is an effect: unloading the fiber takes the definition out again. Any
other form is evaluated as it is, and what it changes is not recorded."
  (let ((head (and (consp form) (car form)))
        (name (and (consp form) (consp (cdr form)) (second form))))
    (cond ((and (member head '(defun defmacro)) name (symbolp name))
           (define-place (list :function name) (lambda () (eval form)) source))
          ((and (member head '(defparameter defvar)) name (symbolp name)
                (or (eq head 'defparameter) (not (boundp name))))
           (define-place (list :variable name) (lambda () (eval form)) source))
          (t (eval form)))))

(defun top-layer (name kind)
  (let ((rt (runtime)))
    (locked (rt) (second (gethash (list kind name) (runtime-places rt))))))

(defun definition-source (name &optional (kind :function))
  "The source of the newest definition a fiber made of NAME, or nil."
  (let ((layer (top-layer name kind))) (and layer (layer-source layer))))

(defun undo-definition (name &optional (kind :function))
  "Take out the newest definition a fiber made of NAME. True when there was one."
  (let ((layer (top-layer name kind)))
    (and layer (funcall (layer-dispose layer)))))

(defun definitions ()
  "Every definition a fiber holds, as (place fiber-id source), newest of each place first."
  (let ((rt (runtime)))
    (locked (rt)
      (loop for place being the hash-keys of (runtime-places rt) using (hash-value cell)
            append (loop for layer in (cdr cell)
                         collect (list place (fiber-id (layer-fiber layer)) (layer-source layer)))))))

;;; ---- a component in a file ----
;;; The file's first form, after any IN-PACKAGE, is (cordis:component :inject
;;; (keys) :provide (keys)). The rest of its forms are the component's apply:
;;; evaluated in order with EVAL-FORM, so every top-level definition is an
;;; effect.

(defmacro component (&key inject provide wrap)
  (declare (ignore inject provide wrap))
  nil)

(defun file-text (path)
  (with-open-file (in path :external-format :utf-8)
    (let* ((text (make-string (file-length in))) (n (read-sequence text in)))
      (subseq text 0 n))))

(defun md5 (text)
  (format nil "~(~{~2,'0x~}~)" (coerce (sb-md5:md5sum-string text :external-format :utf-8) 'list)))

(defun file-header (text name)
  (let ((*package* (find-package :cl-user)) (pos 0) (eof '#:eof))
    (loop
      (multiple-value-bind (form next) (read-from-string text nil eof :start pos)
        (cond ((and (consp form) (eq (car form) 'in-package))
               (setf *package* (or (find-package (second form))
                                   (fail 'cordis-error "~a: there is no package ~a" name (second form)))))
              ((and (consp form) (eq (car form) 'component))
               (return (rest form)))
              (t (fail 'cordis-error "~a does not start with (cordis:component ...)" name)))
        (setf pos next)))))

(defun load-text (text)
  "Evaluate the forms of TEXT for this fiber, in order."
  (let ((*package* (find-package :cl-user)) (pos 0) (eof '#:eof))
    (loop
      (multiple-value-bind (form next) (read-from-string text nil eof :start pos)
        (when (eq form eof) (return))
        (eval-form form (string-trim '(#\Space #\Newline #\Tab) (subseq text pos next)))
        (setf pos next)))))

(defun file-component (path)
  "The component the file at PATH is, as it reads now."
  (let* ((path (namestring (truename path)))
         (text (file-text path))
         (header (file-header text path)))
    (make-component :name (pathname-name path)
                    :inject (getf header :inject) :provide (getf header :provide)
                    :fingerprint (md5 text)
                    :wrap (getf header :wrap)
                    :apply (lambda (config) (declare (ignore config)) (load-text text)))))

;;; ---- hooks ----
;;; A hook is a name the root declares with its default, the function at the
;;; base of its chain. A component wraps hooks: its :wrap is ((hook . wrapper)
;;; ...), a wrapper being a function designator called with INNER and the input,
;;; INNER being the rest of the chain as a function of one input. CHAIN runs a
;;; hook: the wrappers of the active fibers that wrap it, the first loaded
;;; outermost, over the default. The order and the calls are the core
;;; cordis/hooks' (bendcord's host.chain): a call runs the chain it found when
;;; it started; a fiber's wrapper keeps its place when APPLY-CONFIG puts a new
;;; version in; an inactive fiber is passed over; an INNER called after its call
;;; has ended, or kept from an earlier activation of its fiber, signals
;;; STALE-INNER. A wrapper runs as its fiber; the default as the caller.

(defun define-hook (name default)
  "Declare the hook NAME, a string, with DEFAULT, a function of one input, at the
base of its chain. Declaring it again replaces the default."
  (check-type name string)
  (let ((rt (runtime)))
    (locked (rt) (setf (gethash name (runtime-hooks rt)) default))
    name))

(defun hook-default (rt hook)
  (locked (rt)
    (multiple-value-bind (default has) (gethash hook (runtime-hooks rt))
      (unless has (fail 'unknown-hook "there is no hook ~s" hook))
      default)))

(defun loaded-fiber (rt id)
  (locked (rt) (find id (runtime-loaded rt) :key #'fiber-id :test #'equal)))

(defun chain (hook input)
  "Run the hook HOOK on INPUT: the chain of its wrappers over its default. Its value."
  (let* ((rt (runtime))
         (caller *fiber*)
         (default (hook-default rt hook))
         (snap (locked (rt)
                 (chains-snapshot (runtime-chains rt) hook
                                  (lambda (id) (let ((f (loaded-fiber rt id))) (and f (fiber-active f))))))))
    (run-link rt hook snap (locked (rt) (chains-step (runtime-chains rt) snap 0)) 0 input caller default)))

(defun run-link (rt hook snap link position input caller default)
  "Run LINK, at POSITION of SNAP, on INPUT: the default, or a fiber's wrapper with a token for the rest."
  (if (eq (first link) :default)
      (let ((*fiber* caller)) (funcall default input))
      (let* ((id (second link))
             (fiber (loaded-fiber rt id))

             (wrapper (and fiber (cdr (assoc hook (component-wrap (fiber-component fiber)) :test #'equal))))
             (token (and wrapper (locked (rt) (chains-open (runtime-chains rt) id snap position)))))

        (unless token (fail 'cordis-error "~a, which wraps ~s, is not active" id hook))
        (unwind-protect


             (let ((*fiber* fiber))
               (funcall wrapper
                        (lambda (input) (next-link rt hook id snap token input caller default))
                        input))
          (locked (rt) (chains-end (runtime-chains rt) id token))))))

(defun next-link (rt hook id snap token input caller default)
  "What the INNER of ID's wrapper runs: the rest of its own call's chain, or STALE-INNER."
  (let ((r (locked (rt) (chains-resolve (runtime-chains rt) id token))))
    (case (first r)
      (:resolved (run-link rt hook snap (second r) (cl-cordis.core.hooks:position-of token) input caller default))
      ((nil) (fail 'cordis-error "~a, which wraps ~s, is not active" id hook))
      (t (error 'stale-inner
                :reason (first r)
                :message (format nil "the inner of ~a's wrapper of ~s ~a" id hook
                                 (ecase (first r)
                                   (:ended "was called after its call ended")
                                   (:stale (format nil "comes from an earlier activation of ~a" id))
                                   (:unissued "was never issued"))))))))

(defun chain-of (hook)
  "The fibers that wrap HOOK, in the order they run, as (id state); a fiber that is not active is passed over."
  (let ((rt (runtime)))
    (hook-default rt hook)
    (locked (rt)
      (let ((c (runtime-chains rt)))
        (loop for e in (chains-of c hook)
              for id = (aref (chains-names c) (cl-cordis.core.hooks:entry-plugin e))
              for f = (loaded-fiber rt id)
              collect (list id (if f (fiber-state f) :inactive)))))))

;;; ---- the configuration ----
;;; The entries are what the system is meant to hold. APPLY-CONFIG moves the
;;; running system to them, touching only the entries that differ.

(defun entries ()
  "The ids of the entries the running system was last brought to, in order."
  (mapcar #'entry-id (runtime-entries (runtime))))

(defun apply-config (specs)
  "Bring the running system to SPECS, each a plist: :id, then :file (a
component file) or :component (a component), and optionally :config, :intercept
(USE) and :disabled. An entry whose file, component, config, intercept and disabled are as they were
is left alone; another is taken out and instantiated again. Every spec is read
before anything is changed, and the changes are one operation. What was done, as
(id action)."
  (let* ((rt (runtime)) (plan '()) (done '()))
    (dolist (spec specs)
      (let ((id (getf spec :id)))
        (unless id (fail 'cordis-error "an entry has no :id: ~s" spec))
        (when (find id plan :key #'first :test #'equal)
          (fail 'cordis-error "two entries have the id ~a" id))
        (let* ((disabled (and (getf spec :disabled) t))
               (given (getf spec :component))
               (component (cond (disabled nil)
                                ((getf spec :file) (file-component (getf spec :file)))
                                (given (if (symbolp given) (symbol-value given) given))
                                (t (fail 'cordis-error "the entry ~a names no :file and no :component" id)))))
          (push (list id component
                      (list (and component (or (component-fingerprint component) component))
                            (getf spec :config) disabled (getf spec :intercept))
                      (getf spec :config) (getf spec :intercept))
                plan))))
    (setf plan (nreverse plan))
    ;; The list of entries follows every step, so that a step that fails leaves it true.
    (operate rt
     (lambda ()
    (flet ((take-out (entry)
             (when (entry-fiber entry) (retire (entry-fiber entry)))
             (setf (runtime-entries rt) (remove entry (runtime-entries rt)))))
      (in-fiber (nil)
        (dolist (entry (runtime-entries rt))
          (unless (find (entry-id entry) plan :key #'first :test #'equal)
            (take-out entry)
            (push (list (entry-id entry) :removed) done)))
        (loop for (id component print config intercept) in plan
              for old = (find id (runtime-entries rt) :key #'entry-id :test #'equal)
              do (unless (and old (equal print (entry-print old)))
                   ;; a new version of a loaded entry takes the old one's places in the chains
                   (let ((keep (and old component (entry-fiber old) t)))
                     (when keep (locked (rt) (push id (runtime-replacing rt))))
                     (unwind-protect
                          (progn
                            (when old (take-out old))
                            (push (make-entry :id id :print print
                                              :fiber (and component (use component :config config :id id :intercept intercept)))
                                  (runtime-entries rt)))
                       (when keep
                         (locked (rt)
                           (setf (runtime-replacing rt) (remove id (runtime-replacing rt) :test #'equal))
                           (unless (loaded-fiber rt id) (chains-remove (runtime-chains rt) id))))))
                   (push (list id (cond ((null component) :disabled) (old :rebuilt) (t :loaded))) done)))
        (setf (runtime-entries rt)
              (loop for (id) in plan
                    collect (find id (runtime-entries rt) :key #'entry-id :test #'equal)))))))
    (nreverse done)))

(defun amend-entry (id config)
  "Record CONFIG as the config of the entry ID without rebuilding it: for a
change its component has carried out itself. The next rebuild is given CONFIG,
and APPLY-CONFIG with CONFIG for this entry leaves it alone."
  (let* ((rt (runtime))
         (entry (or (find id (runtime-entries rt) :key #'entry-id :test #'equal)
                    (fail 'cordis-error "there is no entry ~a" id))))
    (locked (rt)
      (setf (second (entry-print entry)) config)
      (when (entry-fiber entry) (setf (fiber-config (entry-fiber entry)) config)))
    config))

;;; ---- what the image holds ----

(defun shape (value)
  (let ((text (handler-case (let ((*print-readably* t) (*print-pretty* nil)) (prin1-to-string value))
                (error () (format nil "#<~a>" (type-of value))))))
    (if (> (length text) 120) (format nil "~a chars, md5 ~a" (length text) (md5 text)) text)))

(defun image (&key packages)
  "What the image holds that a component can change, as (line . object) in a
fixed order: the fibers, the keys, and every function and variable whose name's
home is one of PACKAGES."
  (let ((rt (runtime)) (rows '()))
    (locked (rt)
      (dolist (fiber (runtime-loaded rt))
        (push (list (format nil "fiber ~a ~(~a~)" (fiber-id fiber) (fiber-state fiber))) rows))
      (loop for b being the hash-values of (runtime-store rt)
            when (live-binding rt (binding-key b))
              do (push (list (format nil "key ~s from ~a = ~a" (binding-key b) (fiber-id (binding-fiber b))
                                     (shape (binding-value b))))
                       rows))
      (dolist (package packages)
        (let ((package (find-package package)))
          (do-symbols (symbol package)
            (when (eq (symbol-package symbol) package)
              (let ((name (format nil "~a::~a" (package-name package) (symbol-name symbol))))
                (when (and (fboundp symbol) (not (special-operator-p symbol)))
                  (let ((layer (second (gethash (list :function symbol) (runtime-places rt)))))
                    (push (cons (format nil "function ~a ~a" name
                                        (if layer
                                            (format nil "from ~a, md5 ~a" (fiber-id (layer-fiber layer))
                                                    (md5 (or (layer-source layer) "")))
                                            "as loaded"))
                                (or (macro-function symbol) (fdefinition symbol)))
                          rows)))
                (when (boundp symbol)
                  (push (list (format nil "variable ~a = ~a" name (shape (symbol-value symbol)))) rows))))))))
    (sort (remove-duplicates rows :key #'car :test #'string=) #'string< :key #'car)))

(defun image-lines (image)
  (mapcar #'car image))

(defun image-diff (a b &key identity)
  "The lines that are in one of the images A and B and not in the other, each
after - or +. With IDENTITY, a function both hold under one line but as two
objects is listed too, after !."
  (let ((la (image-lines a)) (lb (image-lines b)))
    (append (mapcar (lambda (l) (format nil "- ~a" l)) (set-difference la lb :test #'string=))
            (mapcar (lambda (l) (format nil "+ ~a" l)) (set-difference lb la :test #'string=))
            (and identity
                 (loop for (line . object) in a
                       for other = (assoc line b :test #'string=)
                       when (and object other (cdr other) (not (eq object (cdr other))))
                         collect (format nil "! ~a" line))))))

;;; ---- the runtime ----

(defun start (&key root)
  "Start the runtime: the root fiber, and the scope the operations run in. ROOT is
the root's keys, each (key value): the only keys the root sets, then and later."
  (when *runtime* (fail 'cordis-error "a cordis runtime is running; (cordis:stop) ends it"))
  (let ((rt (make-runtime)) (ready (sc:make-chan)))
    (setf (runtime-root rt)
          (make-fiber :uid 0 :id "root" :live t :active t
                      :component (make-component :name "root")))
    (loop for (key value) in root
          do (when (member key (runtime-root-keys rt) :test #'equal)
               (fail 'provision-conflict "the root names ~s twice" key))
             (setf (runtime-root-keys rt) (append (runtime-root-keys rt) (list key)))
             (setf (gethash key (runtime-store rt)) (make-binding :key key :value value :fiber (runtime-root rt))))
    (setf (runtime-service rt)
          (sb-thread:make-thread
           (lambda ()
             (ignore-errors
              (sc:with-scope (scope :name "cordis" :on-failure :park)
                (setf (runtime-scope rt) scope)
                (sc:send ready t)
                (sc:recv (runtime-stop rt)))))
           :name "cordis"))
    (sc:recv ready :timeout 10)
    (setf *runtime* rt)
    t))

(defun stop ()
  "Take every fiber out, newest first, undo the root's own effects, and end the
runtime. A parked operation is answered with ABANDON first. The inverses of the
root that failed, as text."
  (let ((rt *runtime*))
    (when rt
      (unwind-protect
           (progn
             (loop repeat 20
                   while (runner-parked-p rt)
                   do (let ((runner (runtime-runner rt)))
                        (if (member 'abandon (sc:task-restarts runner))
                            (answer-and-wait rt runner 'abandon '())
                            (return))))
             (unless (runner-parked-p rt)
               (in-fiber (nil)
                 (operate rt (lambda ()
                               (reconcile rt :removed (locked (rt) (copy-list (runtime-loaded rt))))
                               (undo-ledger rt (runtime-root rt)))))))
        (sc:send (runtime-stop rt) t)
        (sb-thread:join-thread (runtime-service rt) :default nil :timeout 30)
        (setf *runtime* nil))
      (fiber-failures (runtime-root rt)))))
