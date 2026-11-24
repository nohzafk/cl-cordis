;;; The checks of cl-cordis, run by check.sh. DIR, from the environment, is a
;;; directory the checks may write component files in.

(defpackage #:cordis-sandbox (:use #:cl))

(defpackage #:cl-cordis/test
  (:use #:cl)
  (:export #:run-all #:fresh))

(in-package #:cl-cordis/test)

;; What the image holds before any component: the checks' components define over these.
(defun cordis-sandbox::greet () "as loaded")
(defparameter cordis-sandbox::*knob* 1)

(defvar *pass* 0)
(defvar *fail* 0)
(defvar *tests* '())
(defvar *verbose* (member "-v" sb-ext:*posix-argv* :test #'string=))
(defvar *dir* (let ((d (sb-ext:posix-getenv "DIR")))
                (cond ((or (null d) (string= d "")) "/tmp/")
                      ((char= #\/ (char d (1- (length d)))) d)
                      (t (concatenate 'string d "/")))))

(defun ok (name pass &optional detail)
  (if pass (incf *pass*) (incf *fail*))
  (format t "~a ~a~%" (if pass "ok  " "FAIL") name)
  (when (and detail (or (not pass) *verbose*)) (format t "       ~a~%" detail))
  (finish-output)
  ;; mutants.sh: the first failed check is the answer, the rest would only cost time
  (when (and (not pass) (sb-ext:posix-getenv "FIRST_FAIL"))
    (sb-ext:exit :code 1 :abort t)))

;; A check that runs longer than this is failed, and the image ends: a check that hangs holds the
;; runtime, so the checks after it would say nothing. The whole clean run takes under 2 s.
(defvar *check-limit* (let ((s (sb-ext:posix-getenv "CHECK_LIMIT")))
                        (if (and s (string/= s "")) (parse-integer s) 5)))

(defun watch (name done)
  "Start a thread that fails the check NAME and ends the image unless DONE (a cons) is set within the limit."
  (sb-thread:make-thread
   (lambda ()
     (loop repeat (* *check-limit* 100)
           until (car done)
           do (sleep 0.01))
     (unless (car done)
       (format t "FAIL ~a~%       did not end in ~d s (CHECK_LIMIT)~%" name *check-limit*)
       (finish-output)
       (sb-ext:exit :code 1 :abort t)))
   :name "check watchdog"))

(defmacro deftest (name &body body)
  `(push (cons ,name (lambda () ,@body)) *tests*))

(defun wait-for (predicate &optional (seconds 10))
  (loop repeat (* seconds 200)
        do (when (funcall predicate) (return t))
           (sleep 0.005)))

;;; ---- what the checks' components leave behind ----

(defvar *events* '())
(defvar *events-lock* (sb-thread:make-mutex :name "events"))

(defun note (x)
  (sb-thread:with-mutex (*events-lock*) (push x *events*))
  x)

(defun events (&optional without)
  (sb-thread:with-mutex (*events-lock*)
    (remove without (reverse *events*) :test (lambda (w e) (and w (consp e) (eql w (second e)))))))

(defun noted-p (x) (member x (events) :test #'equal))

(defmacro undoable (tag)
  "An effect that notes (:do TAG), with an inverse that notes (:undo TAG)."
  `(cordis:effect (lambda () (note (list :do ,tag)) (lambda () (note (list :undo ,tag))))))

(defmacro with-runtime ((&key root) &body body)
  `(progn
     (sb-thread:with-mutex (*events-lock*) (setf *events* '()))
     (cordis:start :root ,root)
     (unwind-protect (progn ,@body) (cordis:stop))))

(defmacro apply-of (&body body)
  `(lambda (config) (declare (ignorable config)) ,@body))

(defun comp (name &key inject provide apply)
  (cordis:make-component :name name :inject inject :provide provide :apply apply))

(defun states (&rest fibers) (mapcar #'cordis:fiber-state fibers))

(defun put (name text)
  "Write TEXT as the file NAME in the checks' directory; its path."
  (let ((path (concatenate 'string *dir* name)))
    (with-open-file (out path :direction :output :if-exists :supersede :external-format :utf-8)
      (write-string text out))
    path))

(defun sandbox (name) (find-symbol (string-upcase name) :cordis-sandbox))
(defun sandbox-call (name &rest args)
  (let ((s (sandbox name))) (and s (fboundp s) (apply s args))))
(defun sandbox-fbound (name) (let ((s (sandbox name))) (and s (fboundp s) t)))
(defun sandbox-value (name) (let ((s (sandbox name))) (if (and s (boundp s)) (symbol-value s) :unbound)))

;;; ---- effects ----

(deftest "L1"
  (with-runtime ()
    (let ((f (cordis:use (comp "a" :apply (apply-of (undoable 1) (undoable 2) (undoable 3))))))
      (cordis:settle)
      (let ((up (cordis:fiber-state f)))
        (cordis:retire f)
        (ok "L1 a component's effects are undone when it is unloaded, the newest first"
            (and (eq up :active) (eq (cordis:fiber-state f) :inactive) (null (cordis:fibers))
                 (equal (events) '((:do 1) (:do 2) (:do 3) (:undo 3) (:undo 2) (:undo 1))))
            (format nil "~a; ~s" up (events)))
        (let ((refused (handler-case (progn (cordis:in-fiber (f) (undoable :late)) nil)
                         (cordis:cordis-error (e) (princ-to-string e)))))
          (ok "L2 an effect for a component that is not installed is refused before it runs"
              (and refused (search "not installed" refused) (not (noted-p '(:do :late))))
              refused))))))

(deftest "L3"
  (with-runtime ()
    (let ((f (cordis:use (comp "a" :apply (apply-of
                                            (undoable 1)
                                            (cordis:effect (lambda () (lambda () (error "cannot close the file"))))
                                            (undoable 3))))))
      (cordis:settle)
      (cordis:retire f)
      (ok "L3 an inverse that fails is recorded, and the inverses behind it still run"
          (and (equal (events) '((:do 1) (:do 3) (:undo 3) (:undo 1)))
               (= 1 (length (cordis:fiber-failures f)))
               (search "cannot close" (first (cordis:fiber-failures f)))
               (eq (cordis:fiber-state f) :inactive))
          (format nil "~s; failures ~s" (events) (cordis:fiber-failures f))))))

(deftest "N1"
  (with-runtime ()
    (let* ((child nil)
           (parent (cordis:use (comp "parent"
                                     :apply (apply-of
                                              (undoable :p1)
                                              (setf child (cordis:use (comp "child" :apply (apply-of (undoable :c)))))
                                              (undoable :p2))))))
      (cordis:settle)
      (let ((up (states parent child)) (count (length (cordis:fibers))))
        (cordis:retire parent)
        (ok "N1 a component a component instantiates is one of its effects: it is taken out in its turn when the parent is unloaded"
            (and (equal up '(:active :active)) (= count 2) (null (cordis:fibers))
                 (equal (events :c) '((:do :p1) (:do :p2) (:undo :p2) (:undo :p1)))
                 (equal (member '(:undo :p2) (events) :test #'equal) '((:undo :p2) (:undo :c) (:undo :p1))))
            (format nil "~s" (events)))))))

(deftest "N2"
  (with-runtime ()
    (let* ((child nil)
           (parent (cordis:use (comp "parent"
                                     :apply (apply-of
                                              (setf child (cordis:use (comp "child" :provide '(:ck)
                                                                            :apply (apply-of (cordis:provide :ck 1) (undoable :c)))))))))
           (reader (cordis:use (comp "reader" :inject '(:ck) :apply (apply-of (undoable :r))))))
      (cordis:settle)
      (let ((up (states parent child reader)))
        (cordis:retire parent)
        (ok "N2 what reads a key a child provides stops before the parent's inverses run, the child's among them"
            (and (equal up '(:active :active :active))
                 (equal (events) '((:do :c) (:do :r) (:undo :r) (:undo :c)))
                 (eq (cordis:fiber-state reader) :inactive)
                 (equal (mapcar #'cordis:fiber-id (cordis:fibers)) '("reader")))
            (format nil "~s ~s ~s" up (events) (mapcar #'cordis:fiber-id (cordis:fibers))))))))

;;; ---- coeffects ----

(defun db-component (url)
  (comp "db" :provide '(:db) :apply (apply-of (cordis:provide :db url) (undoable :pool))))

(deftest "C1"
  (with-runtime ()
    (let* ((app (cordis:use (comp "app" :inject '(:db)
                                  :apply (apply-of
                                           (note (list :app-up (cordis:inject :db)))
                                           (cordis:effect
                                            (lambda () (lambda () (note (list :app-down (cordis:inject :db))))))))))
           (before (progn (cordis:settle) (cordis:fiber-state app)))
           (why (cordis:blocked))
           (db (cordis:use (db-component "pg"))))
      (cordis:settle)
      (ok "C1 a component that needs a key waits until a component provides it, and is installed then; no order of loading is arranged"
          (and (eq before :inactive) (equal why '(("app" :missing :db)))
               (equal (states app db) '(:active :active))
               (equal (events) '((:do :pool) (:app-up "pg"))))
          (format nil "~a ~s; ~s; ~s" before why (states app db) (events)))
      (cordis:retire db)
      (ok "C2 when a provider leaves, what needs it is unloaded first and still reads the key in its own inverses; then the provider's inverses run"
          (and (eq (cordis:fiber-state app) :inactive)
               (equal (nthcdr 2 (events)) '((:app-down "pg") (:undo :pool))))
          (format nil "~s" (events)))
      (cordis:use (db-component "pg2"))
      (cordis:settle)
      (ok "C3 the key is provided again by another fiber: what needs it is installed again, against the new one"
          (and (eq (cordis:fiber-state app) :active) (equal (car (last (events))) '(:app-up "pg2")))
          (format nil "~s" (events))))))

(deftest "C4"
  (with-runtime (:root '((:mine 0)))
    (let* ((a (cordis:use (comp "a" :provide '(:k) :apply (apply-of (cordis:provide :k 1)))))
           (second (handler-case (progn (cordis:use (comp "b" :provide '(:k))) nil)
                     (cordis:provision-conflict (e) (princ-to-string e))))
           (same-id (handler-case (progn (cordis:use (comp "a")) nil)
                      (cordis:duplicate-id (e) (princ-to-string e))))
           (by-root (handler-case (progn (cordis:provide :k 2) nil)
                      (cordis:not-root (e) (princ-to-string e))))
           (over-root (handler-case (progn (cordis:use (comp "c" :provide '(:mine))) nil)
                        (cordis:provision-conflict (e) (princ-to-string e)))))
      (cordis:settle)
      (ok "C4 a key has one source: a second component that declares it, a second fiber with a loaded id, a component that declares a root key, and the root setting a key it was not started with are refused, and nothing changes"
          (and (eq (cordis:fiber-state a) :active)
               second (search "provides already" second)
               same-id (search "loaded already" same-id)
               by-root (search "is not a root key" by-root)
               over-root (search "provides already" over-root)
               (equal (multiple-value-list (cordis:value :mine)) '(0 t))
               (= 1 (length (cordis:fibers)))
               (equal (multiple-value-list (cordis:value :k)) '(1 t)))
          (format nil "~a; ~a; ~a; ~a" second same-id by-root over-root)))
    (let ((peek (cordis:use (comp "peek" :apply (apply-of (note (list :read (cordis:inject :k))))))))
      (let ((report (first (cordis:parked-report))))
        (cordis:respond peek 'cordis:abandon)
        (let ((rogue (cordis:use (comp "rogue" :apply (apply-of (cordis:provide :z 1))))))
          (let ((report2 (first (cordis:parked-report))))
            (cordis:respond rogue 'cordis:abandon)
            (cordis:settle)
            (ok "C6 a component that reads a key, or sets one, that it does not declare stops there"
                (and (equal (getf report :id) "peek") (search "does not declare" (getf report :error))
                     (equal (getf report2 :id) "rogue") (search "without declaring" (getf report2 :error))
                     (typep (cordis:fiber-error peek) 'cordis:undeclared-access)
                     (equal (states peek rogue) '(:failed :failed))
                     (not (noted-p '(:read 1)))
                     (equal (multiple-value-list (cordis:value :z)) '(nil nil)))
                (format nil "~s; ~s; ~s" report report2 (states peek rogue)))))))))

(deftest "C7"
  (with-runtime (:root '((:root-key 1)))
    (let* ((a (cordis:use (comp "a" :provide '(:k) :apply (apply-of (cordis:provide :k 1) (cordis:provide :k 2)))))
           (r (cordis:use (comp "r" :inject '(:k)
                                :apply (apply-of (note (list :up (cordis:inject :k)))
                                                 (cordis:effect (lambda () (lambda () (note (list :down (cordis:inject :k)))))))))))
      (cordis:settle)
      (let ((first (events)))
        (cordis:in-fiber (a) (cordis:provide :k 3))
        (let ((after (events)))
          (let ((r2 (cordis:use (comp "r2" :inject '(:root-key)
                                      :apply (apply-of (note (list :r2 (cordis:inject :root-key))))))))
            (cordis:provide :root-key 2)
            (ok "C7 a component sets its key again: while it activates, nothing restarts; once it is active, what reads the key restarts, before the set returns, and reads the new value; a key the root sets again restarts its readers too"
                (and (equal first '((:up 2)))
                     (equal after '((:up 2) (:down 2) (:up 3)))
                     (equal (states a r r2) '(:active :active :active))
                     (equal (remove-if-not (lambda (e) (eq (first e) :r2)) (events)) '((:r2 1) (:r2 2))))
                (format nil "~s; ~s; ~s" first after (events)))))))))

(deftest "C8"
  (with-runtime ()
    (let ((lazy (cordis:use (comp "lazy" :provide '(:k :j) :apply (apply-of (undoable :l) (cordis:provide :k 1))))))
      (let ((report (first (cordis:parked-report))))
        (cordis:respond lazy 'cordis:abandon)
        (cordis:settle)
        (ok "C8 a component whose apply returns without setting a key it provides stops there; ABANDON undoes what it did and leaves it failed"
            (and (equal (getf report :id) "lazy")
                 (search "returned without setting :J" (getf report :error))
                 (eq (cordis:fiber-state lazy) :failed)
                 (equal (events) '((:do :l) (:undo :l)))
                 (equal (multiple-value-list (cordis:value :k)) '(nil nil)))
            (format nil "~s; ~s ~s" report (cordis:fiber-state lazy) (events)))))))

(deftest "C5"
  (with-runtime ()
    (let ((a (cordis:use (comp "a" :inject '(:b) :provide '(:a) :apply (apply-of (cordis:provide :a 1)))))

          (b (cordis:use (comp "b" :inject '(:a) :provide '(:b) :apply (apply-of (cordis:provide :b 2)))))
          (c (cordis:use (comp "c" :apply (apply-of (undoable :c)))))
          (d (cordis:use (comp "d" :inject '(:b)))))
      (cordis:settle)
      (ok "C5 two components that need each other are never installed, and are named; the others are not held up"
          (and (equal (states a b c d) '(:inactive :inactive :active :inactive))
               (equal (cordis:blocked) '(("a" :cycle) ("b" :cycle) ("d" :waits :b "b"))))
          (format nil "~s ~s" (states a b c d) (cordis:blocked))))))

;;; ---- one operation at a time ----

(deftest "O1"
  (with-runtime ()
    (let* ((gate (sc:make-chan))
           (db (cordis:use (db-component "pg")))
           (app nil)
           (loader (sb-thread:make-thread
                    (lambda ()
                      (setf app (cordis:use (comp "app" :inject '(:db)
                                                  :apply (apply-of (undoable 1) (sc:recv gate) (undoable 2)))))))))
      (wait-for (lambda () (noted-p '(:do 1))))
      (let ((leaver (sb-thread:make-thread (lambda () (cordis:retire db)))))
        (sleep 0.05)
        (let ((held (events)) (during (cordis:fiber-state db)))
          (sc:send gate t)
          (sb-thread:join-thread loader)
          (sb-thread:join-thread leaver)
          (ok "O1 one operation runs at a time: a provider taken out while a reader activates waits for that activation, then the reader stops first"
              (and (equal held '((:do :pool) (:do 1))) (eq during :active)
                   (equal (events) '((:do :pool) (:do 1) (:do 2) (:undo 2) (:undo 1) (:undo :pool)))
                   (eq (cordis:fiber-state app) :inactive)
                   (equal (mapcar #'cordis:fiber-id (cordis:fibers)) '("app")))
              (format nil "held ~s ~a; ~s" held during (events))))))))

(deftest "O2"
  (with-runtime ()
    (let* ((svc (cordis:use (comp "svc" :apply (apply-of (undoable 1) (error "the port is taken")))))
           (queued nil)
           (refusals (list (handler-case (progn (cordis:use (comp "other")) nil)
                             (cordis:component-parked (e) (princ-to-string e)))
                           (handler-case (progn (cordis:retire svc) nil)
                             (cordis:component-parked (e) (princ-to-string e)))
                           (handler-case (progn (cordis:provide :k 1) nil)
                             (cordis:component-parked (e) (princ-to-string e))))))
      (let ((held (list (cordis:fiber-state svc) (length (cordis:fibers)) (events))))
        (cordis:respond svc 'cordis:abandon)
        (setf queued (cordis:use (comp "other" :apply (apply-of (undoable :o)))))
        (cordis:retire svc)
        (ok "O2 while an apply is parked, every other operation is refused at once and changes nothing; once it is answered they run again"
            (and (every (lambda (r) (and r (search "svc is parked" r))) refusals)
                 (equal held '(:loading 1 ((:do 1))))
                 (eq (cordis:fiber-state queued) :active)
                 (equal (mapcar #'cordis:fiber-id (cordis:fibers)) '("other"))
                 (equal (events) '((:do 1) (:undo 1) (:do :o))))
            (format nil "~s; held ~s; ~s" refusals held (events)))))))

(deftest "O3"
  (with-runtime ()
    (let* ((gate (sc:make-chan))
           (refused nil) (late nil)
           (first (sb-thread:make-thread
                   (lambda ()
                     (cordis:use (comp "slow" :apply (apply-of (when (eq (sc:recv gate) :fail) (error "it broke")))))))))
      (wait-for (lambda () (cordis:find-fiber "slow")))
      (let ((waiter (sb-thread:make-thread
                     (lambda ()
                       (handler-case (setf late (cordis:use (comp "late")))
                         (cordis:component-parked (e) (setf refused (princ-to-string e))))))))
        (sleep 0.05)
        (sc:send gate :fail)
        (sb-thread:join-thread waiter)
        (sb-thread:join-thread first)
        (let ((loaded (mapcar #'cordis:fiber-id (cordis:fibers))))
          (cordis:respond "slow" 'cordis:abandon)
          (cordis:settle)
          (ok "O3 an operation queued behind one that then parks is refused as well, and is not run after the answer"
              (and refused (search "slow is parked" refused) (null late)
                   (equal loaded '("slow"))
                   (equal (mapcar #'cordis:fiber-id (cordis:fibers)) '("slow")))
              (format nil "~a ~s ~s" refused loaded (mapcar #'cordis:fiber-id (cordis:fibers)))))))))

;;; ---- observing: bendcord's watch, changes, status, active, faults ----

(deftest "O1"
  (with-runtime (:root '((:r 1)))
    (let* ((listener (lambda (key) (note (list :wrote key (nth-value 1 (cordis:value key))))))
           (off (cordis:watch listener))
           (a (cordis:use (comp "a" :provide '(:k :j) :apply (apply-of (cordis:provide :j 1) (cordis:provide :k 1))))))
      (cordis:settle)
      (cordis:provide :r 2)
      (let ((off2 (cordis:watch listener)))
        (cordis:in-fiber (a) (cordis:provide :k 2))
        (funcall off2))
      (cordis:retire a)
      (cordis:settle)
      (funcall off)
      (cordis:provide :r 3)
      (ok "O1 a watcher is called with the key at each write: a component's set, the root's set, and at a stop one clear for each key the component declares, in the order it declares them, the key already empty; a listener registered twice is called twice, and each registration is removed alone"
          (equal (events) '((:wrote :j nil) (:wrote :k nil) (:wrote :r t)
                            (:wrote :k t) (:wrote :k t)
                            (:wrote :k nil) (:wrote :j nil)))
          (format nil "~s" (events))))))

(deftest "O2"
  (with-runtime ()
    (let* ((off (cordis:changes :k (lambda (value present) (note (list :k value present)))))
           (a (cordis:use (comp "a" :provide '(:k :other)
                                    :apply (apply-of (cordis:provide :k 1) (cordis:provide :other 9) (cordis:provide :k 2))))))
      (cordis:settle)
      (cordis:retire a)
      (cordis:settle)
      (funcall off)
      (let ((b (cordis:use (comp "b" :provide '(:k) :apply (apply-of (cordis:provide :k 3))))) (late '()))
        (cordis:settle)
        (funcall (cordis:changes :k (lambda (value present) (push (list value present) late))))
        (cordis:retire b)
        (ok "O2 changes tells what a key holds now, then after each write to that key and no other: each set, a set while the component activates too, and the clear at its stop; ended, it tells nothing more; started on a key that is set, it tells the value first"
            (and (equal (events) '((:k nil nil) (:k 1 t) (:k 2 t) (:k nil nil)))
                 (equal late '((3 t))))
            (format nil "~s; ~s" (events) late))))))

(deftest "O3"
  (with-runtime ()
    (let* ((none (multiple-value-list (cordis:status "late")))
           (late (cordis:use (comp "late" :inject '(:k) :apply (apply-of nil))))
           (waiting (list (cordis:status "late") (cordis:active)))
           (bad (cordis:use (comp "bad" :apply (apply-of (error "no disk")))))
           (parked (cordis:status "bad")))
      (declare (ignorable late))
      (cordis:respond bad 'cordis:abandon)
      (cordis:use (comp "a" :provide '(:k) :apply (apply-of (cordis:provide :k 1))))
      (cordis:settle)
      (multiple-value-bind (state why) (cordis:status "bad")
        (ok "O3 status is nil for an id that is not loaded, :blocked for a component that waits for a key or is still in its apply, :active once it is, :failed with why once it failed; active lists the active ids in the order they activated, not the order they were loaded"
            (and (equal none '(nil))
                 (equal waiting '(:blocked nil))
                 (eq parked :blocked)
                 (eq state :failed) (search "no disk" (princ-to-string why))
                 (equal (list (cordis:status "a") (cordis:status "late")) '(:active :active))
                 (equal (cordis:active) '("a" "late")))
            (format nil "~s ~s ~s ~s ~s ~s" none waiting parked state why (cordis:active)))))))

(deftest "O4"
  (with-runtime ()
    (let* ((x (cordis:use (comp "x" :apply (apply-of (undoable 1)
                                                     (cordis:effect (lambda () (lambda () (error "cannot close x"))))
                                                     (undoable 2)))))
           (y (cordis:use (comp "y" :apply (apply-of (cordis:effect (lambda () (lambda () (error "cannot close y")))))))))
      (cordis:settle)
      (let ((before (cordis:faults)))
        (cordis:retire x)
        (cordis:settle)
        (let ((one (cordis:faults)))
          (cordis:retire y)
          (cordis:settle)
          (ok "O4 faults lists every inverse that failed while its component stopped, with the component's id, oldest first; the component's other inverses still ran"
              (and (null before)
                   (equal one '(("x" . "cannot close x")))
                   (equal (cordis:faults) '(("x" . "cannot close x") ("y" . "cannot close y")))
                   (equal (events) '((:do 1) (:do 2) (:undo 2) (:undo 1))))
              (format nil "~s ~s ~s; ~s" before one (cordis:faults) (events))))))))

;;; ---- a component that fails ----

(deftest "F1"
  (with-runtime (:root '((:cfg 1)))
    (let* ((steady (cordis:use (comp "steady" :apply (apply-of (undoable :s)))))
           (svc (cordis:use (comp "svc" :inject '(:cfg) :apply (apply-of (undoable 1) (undoable 2)
                                                                       (error "the port is taken")
                                                                       (undoable 3))))))
      (let ((report (first (cordis:parked-report))) (held (events :s)))
        (cordis:respond svc 'cordis:abandon)
        (cordis:settle)
        (ok "F1 a component whose apply fails stops where it failed, with nothing undone; ABANDON undoes what it had done and leaves it failed; the others go on"
            (and report (equal (getf report :id) "svc") (search "port is taken" (getf report :error))
                 (member 'cordis:abandon (getf report :restarts)) (member 'cordis:retry (getf report :restarts))
                 (getf report :stack)
                 (equal held '((:do 1) (:do 2)))
                 (equal (events :s) '((:do 1) (:do 2) (:undo 2) (:undo 1)))
                 (equal (states svc steady) '(:failed :active))
                 (search "port" (princ-to-string (cordis:fiber-error svc)))
                 (null (cordis:parked))
                 (equal (first (first (cordis:blocked))) "svc") (eq (second (first (cordis:blocked))) :failed))
            (format nil "~s~%       held ~s; ~s; ~s" report held (events :s) (states svc steady)))
        ;; what it reads changes
        (cordis:provide :cfg 2)
        (cordis:settle)
        (let ((stays (list (cordis:fiber-state svc) (length (cordis:parked)) (count '(:do 1) (events) :test #'equal))))
          (cordis:revive svc)
          (cordis:settle)
          (let ((again (length (cordis:parked))))
            (cordis:respond svc 'cordis:abandon)
            (cordis:settle)
            (ok "F2 a failed component stays out when what it reads changes; REVIVE lets it activate again"
                (and (equal stays '(:failed 0 1))
                     (= again 1) (eq (cordis:fiber-state svc) :failed)
                     (= 2 (count '(:do 1) (events) :test #'equal)))
                (format nil "stays ~s; parked again ~a; ~s" stays again (events :s)))))))))

(deftest "F3"
  (with-runtime ()
    (let ((svc (cordis:use (comp "svc" :apply (apply-of
                                                (undoable 1)
                                                (note (list :got (restart-case (error "no credential")
                                                                   (use-value (v) v))))
                                                (undoable 2))))))
      (cordis:settle)
      (let ((offered (getf (first (cordis:parked-report)) :restarts)))
        (cordis:respond svc 'use-value "CRED")
        (cordis:settle)
        (ok "F3 a parked component is answered with a restart of its own code: it goes on from the failed form, and what it had installed is not installed twice"
            (and (member 'use-value offered)
                 (eq (cordis:fiber-state svc) :active)
                 (equal (events) '((:do 1) (:got "CRED") (:do 2))))
            (format nil "~s; ~a ~s" offered (cordis:fiber-state svc) (events)))))))

(deftest "F4"
  (with-runtime ()
    (setf (fdefinition 'cordis-sandbox::port) (lambda () (error "the port is taken")))
    (unwind-protect
         (let ((svc (cordis:use (comp "svc" :apply (apply-of
                                                     (undoable 1)
                                                     (note (list :port (funcall 'cordis-sandbox::port))))))))
           (cordis:settle)
           (let ((parked (length (cordis:parked))))
             (setf (fdefinition 'cordis-sandbox::port) (lambda () 8080))
             (cordis:respond svc 'cordis:retry)
             (cordis:settle)
             (ok "F4 a function is redefined while a component is parked; RETRY undoes what it had installed and installs it again with the new function"
                 (and (= parked 1) (eq (cordis:fiber-state svc) :active)
                      (equal (events) '((:do 1) (:undo 1) (:do 1) (:port 8080))))
                 (format nil "~a ~s" (cordis:fiber-state svc) (events)))))
      (fmakunbound 'cordis-sandbox::port))))

(deftest "F5"
  (with-runtime ()
    (let ((svc (cordis:use (comp "svc" :apply (apply-of (undoable 1) (error "the port is taken"))))))
      (let* ((parked (length (cordis:parked)))
             (refused (handler-case (progn (cordis:retire svc) nil)
                        (cordis:component-parked (e) (princ-to-string e)))))
        (cordis:respond svc 'cordis:abandon)
        (cordis:retire svc)
        (ok "F5 a parked component is taken out after it is answered: RETIRE is refused while it is parked, and takes it out after ABANDON"
            (and (= parked 1) refused (null (cordis:parked)) (null (cordis:fibers))
                 (equal (events) '((:do 1) (:undo 1))))
            (format nil "~a ~s" refused (events)))))))

(deftest "R1"
  (with-runtime ()
    (let* ((n 0)
           (db (cordis:use (comp "db" :provide '(:db)
                                 :apply (apply-of (cordis:provide :db (incf n)) (undoable :pool)))))
           (app (cordis:use (comp "app" :inject '(:db)
                                  :apply (apply-of
                                           (note (list :app-up (cordis:inject :db)))
                                           (cordis:effect (lambda () (lambda () (note :app-down)))))))))
      (cordis:settle)
      (cordis:rebuild db)
      (cordis:settle)
      (ok "R1 REBUILD unloads a fiber and installs it again: what needs it is unloaded first and installed again after, and the fibers are the same"
          (and (equal (states db app) '(:active :active))
               (eq db (cordis:find-fiber "db")) (eq app (cordis:find-fiber "app"))
               (equal (events) '((:do :pool) (:app-up 1) :app-down (:undo :pool) (:do :pool) (:app-up 2))))
          (format nil "~s ~s" (states db app) (events))))))

;;; ---- a thread ----

(defun threads-named (name)
  (count name (sb-thread:list-all-threads) :key #'sb-thread:thread-name :test #'equal))

(deftest "T1"
  (with-runtime ()
    (let ((f (cordis:use (comp "ticker" :apply (apply-of
                                                 (cordis:thread (lambda ()
                                                                  (undoable :from-thread)
                                                                  (loop (note :tick) (sc:pause 0.01)))
                                                                :name "ticker thread"))))))
      (cordis:settle)
      (wait-for (lambda () (> (count :tick (events)) 3)))
      (let ((running (threads-named "ticker thread")))
        (cordis:retire f)
        (let ((ticks (count :tick (events))))
          (sleep 0.1)
          (ok "T1 a thread a component starts is one of its effects: unloading cancels it where it waits and waits for it; an effect made in the thread is the component's"
              (and (= running 1) (zerop (threads-named "ticker thread"))
                   (= ticks (count :tick (events)))
                   (noted-p '(:undo :from-thread)))
              (format nil "running ~a, after ~a; ticks ~a then ~a" running (threads-named "ticker thread")
                      ticks (count :tick (events)))))))))

;;; ---- definitions ----

(defun definer (name &rest texts)
  (comp name :apply (apply-of (dolist (text texts) (cordis:eval-form (read-from-string text) text)))))

(deftest "D1"
  (with-runtime ()
    (let ((as-loaded #'cordis-sandbox::greet) (seen '()))
      (flet ((see () (push (list (sandbox-call "greet") (sandbox-fbound "extra-a")) seen)))
        (let ((a (cordis:use (definer "a" "(defun cordis-sandbox::greet () \"from a\")"
                               "(defun cordis-sandbox::extra-a () 1)"))))
          (cordis:settle)
          (let ((b (cordis:use (definer "b" "(defun cordis-sandbox::greet () \"from b\")"))))
            (cordis:settle)
            (see)
            (cordis:retire a) (see)
            (cordis:retire b) (see)))
        (let ((first-order (reverse seen)) (back (eq as-loaded #'cordis-sandbox::greet)))
          (setf seen '())
          (let ((a (cordis:use (definer "a" "(defun cordis-sandbox::greet () \"from a\")"))))
            (cordis:settle)
            (let ((b (cordis:use (definer "b" "(defun cordis-sandbox::greet () \"from b\")"))))
              (cordis:settle)
              (cordis:retire b) (see)
              (cordis:retire a) (see)))
          (ok "D1 two components define one function: whichever leaves first, the function is the other's, and with both gone it is the function the image had"
              (and (equal first-order '(("from b" t) ("from b" nil) ("as loaded" nil)))
                   back
                   (equal (reverse seen) '(("from a" nil) ("as loaded" nil)))
                   (eq as-loaded #'cordis-sandbox::greet)
                   (null (cordis:definitions)))
              (format nil "~s ~a; ~s" first-order back (reverse seen))))))))

(deftest "D3"
  (with-runtime ()
    (let* ((take-out nil)
           (f (cordis:use (comp "binder"
                                :apply (apply-of
                                         (cordis:bind-function 'cordis-sandbox::greet (lambda () "bound"))
                                         (setf take-out (cordis:bind-function 'cordis-sandbox::extra (lambda () 2))))))))
      (cordis:settle)
      (let ((during (list (sandbox-call "greet") (sandbox-call "extra"))))
        (funcall take-out)
        (let ((early (sandbox-fbound "extra")))
          (cordis:retire f)
          (ok "D3 a function bound by a component is taken out with it, or before it by the function BIND-FUNCTION returns"
              (and (equal during '("bound" 2)) (not early) (equal (sandbox-call "greet") "as loaded"))
              (format nil "~s ~a ~s" during early (sandbox-call "greet"))))))))

(deftest "D2"
  (with-runtime ()
    (let ((f (cordis:use (definer "vars" "(defparameter cordis-sandbox::*knob* 7)"

                           "(defparameter cordis-sandbox::*knob* 2)"
                           "(defvar cordis-sandbox::*fresh* 5)"
                           "(defmacro cordis-sandbox::twice (x) (list '* 2 x))"))))
      (cordis:settle)
      (let ((during (list (sandbox-value "*knob*") (sandbox-value "*fresh*")
                          (and (sandbox-fbound "twice") (eval (list (sandbox "twice") 21)))
                          (cordis:definition-source 'cordis-sandbox::twice)
                          (count '(:variable cordis-sandbox::*knob*) (cordis:definitions) :key #'first :test #'equal))))
        (cordis:retire f)
        (ok "D2 a variable and a macro a component defines are taken out with it: the variable has the value it had, or none; a variable set twice is held once"
            (and (equal during '(2 5 42 "(defmacro cordis-sandbox::twice (x) (list '* 2 x))" 1))
                 (equal (list (sandbox-value "*knob*") (sandbox-value "*fresh*") (sandbox-fbound "twice"))
                        '(1 :unbound nil)))
            (format nil "~s; then ~s" during
                    (list (sandbox-value "*knob*") (sandbox-value "*fresh*") (sandbox-fbound "twice"))))))))

;;; ---- components in files, and the configuration ----

(defun db-file (url)
  (put "db.lisp" (format nil "(in-package :cordis-sandbox)~%(cordis:component :provide (:db))~%(defun db-url () ~s)~%(cordis:provide :db (db-url))~%" url)))

(defun app-file ()
  (put "app.lisp" "(in-package :cordis-sandbox)
(cordis:component :inject (:db))
(defparameter *app-db* (cordis:inject :db))
(defun app-banner () (format nil \"app on ~a\" *app-db*))
"))

(defun log-file ()
  (put "log.lisp" "(in-package :cordis-sandbox)
(cordis:component)
(cl-cordis/test::note :log-loaded)
(defun log-line (x) (format nil \"log: ~a\" x))
"))

(defun specs (&rest ids)
  (loop for id in ids
        collect (if (consp id)
                    (list :id (first id) :file (concatenate 'string *dir* (first id) ".lisp") :disabled t)
                    (list :id id :file (concatenate 'string *dir* id ".lisp")))))

(deftest "E1"
  (with-runtime ()
    (db-file "pg://1") (app-file) (log-file)
    (let* ((did (cordis:apply-config (specs "app" "log" "db")))
           (settled (cordis:settle))
           (app (cordis:find-fiber "app")) (logger (cordis:find-fiber "log"))
           (first (list (sandbox-call "app-banner") (sandbox-call "log-line" 1))))
      (db-file "pg://2")
      (let ((again (cordis:apply-config (specs "app" "log" "db"))))
        (cordis:settle)
        (ok "E1 components in files are loaded from a list in any order; after one file changes, the same list rebuilds that entry alone, and what needs it is installed again"
            (and settled
                 (equal did '(("app" :loaded) ("log" :loaded) ("db" :loaded)))
                 (equal first '("app on pg://1" "log: 1"))
                 (equal again '(("db" :rebuilt)))
                 (equal (sandbox-call "app-banner") "app on pg://2")
                 (eq app (cordis:find-fiber "app")) (eq logger (cordis:find-fiber "log"))
                 (= 1 (count :log-loaded (events)))
                 (equal (cordis:apply-config (specs "app" "log" "db")) '()))
            (format nil "~s ~s; ~s ~s" did first again (sandbox-call "app-banner"))))
      (let* ((removed (cordis:apply-config (specs "app" "db")))
             (no-log (not (sandbox-fbound "log-line")))
             (off (cordis:apply-config (specs '("app") "db")))
             (no-app (not (sandbox-fbound "app-banner")))
             (on (cordis:apply-config (specs "app" "db"))))
        (cordis:settle)
        (ok "E2 an entry left out of the list is taken out, and one marked disabled is unloaded until the mark is cleared"
            (and (equal removed '(("log" :removed))) no-log
                 (equal off '(("app" :disabled))) no-app
                 (equal on '(("app" :rebuilt))) (equal (sandbox-call "app-banner") "app on pg://2")
                 (equal (cordis:entries) '("app" "db")))
            (format nil "~s ~a; ~s ~a; ~s" removed no-log off no-app on)))
      (put "broken.lisp" "(in-package :cordis-sandbox)\n(defun no-header () 1)\n")
      (let ((refused (handler-case (progn (cordis:apply-config (specs "broken" "db")) nil)
                       (cordis:cordis-error (e) (princ-to-string e)))))
        (ok "E3 a list with a file that cannot be a component is refused before anything is changed"
            (and refused (search "does not start with" refused)
                 (equal (cordis:entries) '("app" "db"))
                 (equal (sandbox-call "app-banner") "app on pg://2"))
            refused)))))

(deftest "E8"
  (with-runtime ()
    (let* ((seen '())
           (c (comp "svc" :apply (lambda (config) (push (getf config :n) seen)))))
      (cordis:apply-config (list (list :id "svc" :component c :config '(:n 1))))
      (cordis:settle)
      (cordis:amend-entry "svc" '(:n 2))
      (let ((same (cordis:apply-config (list (list :id "svc" :component c :config '(:n 2))))))
        (cordis:rebuild (cordis:find-fiber "svc"))
        (ok "E8 an entry's config is amended without a rebuild: the same config then changes nothing, and the next rebuild is given it"
            (and (null same) (equal (reverse seen) '(1 2)))
            (format nil "~s ~s" same (reverse seen)))))))

(defparameter *packages* '(:cordis-sandbox))

(defun write-lines (name lines)
  (put name (format nil "~{~a~%~}" lines)))

(deftest "E4"
  (let (before after live direct)
    (cordis:start)
    (unwind-protect
         (progn
           (setf before (cordis:image :packages *packages*))
           ;; a history: load, change a file, take out, disable, bring back, change again
           (db-file "pg://1") (app-file) (log-file)
           (cordis:apply-config (specs "log" "app"))
           (cordis:apply-config (specs "db" "app" "log"))
           (cordis:settle)
           (db-file "pg://2")
           (cordis:apply-config (specs "db" '("app")))
           (cordis:settle)
           (cordis:apply-config (specs '("db") "app" "log"))
           (cordis:settle)
           (db-file "pg://3")
           (cordis:apply-config (specs "app" "db" "log"))
           (cordis:settle)
           (setf live (cordis:image :packages *packages*)))
      (cordis:stop))
    (cordis:start)
    (unwind-protect
         (progn
           (setf after (cordis:image :packages *packages*))
           (cordis:apply-config (specs "app" "db" "log"))
           (cordis:settle)
           (setf direct (cordis:image :packages *packages*)))
      (cordis:stop))
    (write-lines "live.image" (cordis:image-lines live))
    (with-open-file (out (concatenate 'string *dir* "final.specs") :direction :output :if-exists :supersede)
      (prin1 (specs "app" "db" "log") out))
    (ok "E4 with every component taken out, the image holds what it held before the first: the same functions, the same values"
        (and before (null (cordis:image-diff before after :identity t)))
        (format nil "~{~a~^~%       ~}" (cordis:image-diff before after :identity t)))
    (ok "E5 after a history of loads, changes and removals, the image holds what loading the last list alone gives"
        (and live (find "function CORDIS-SANDBOX::APP-BANNER" (cordis:image-lines live) :test #'search)
             (find "pg://3" (cordis:image-lines live) :test #'search)
             (null (cordis:image-diff live direct)))
        (format nil "~{~a~^~%       ~}" (or (cordis:image-diff live direct) (cordis:image-lines live))))))

(deftest "E6"
  (with-runtime ()
    (put "leaky.lisp" "(in-package :cordis-sandbox)
(cordis:component)
(defun honest () 1)
(setf (symbol-function 'sneaky) (lambda () 2))
(setf *knob* 99)
")
    (let ((before (cordis:image :packages *packages*)))
      (cordis:apply-config (specs "leaky"))
      (cordis:settle)
      (cordis:apply-config '())
      (let ((diff (cordis:image-diff before (cordis:image :packages *packages*) :identity t)))
        (fmakunbound 'cordis-sandbox::sneaky)
        (setf cordis-sandbox::*knob* 1)
        (ok "E6 what a component changes outside its effects stays after it: the comparison of the image names each such change"
            (equal (sort (copy-list diff) #'string<)
                   '("+ function CORDIS-SANDBOX::SNEAKY as loaded"
                     "+ variable CORDIS-SANDBOX::*KNOB* = 99"
                     "- variable CORDIS-SANDBOX::*KNOB* = 1"))
            (format nil "~s" diff))))))

;;; ---- the cores, against bendcord's TypeScript ----

(defun case-file ()
  (with-open-file (in (merge-pathnames "test/cases/cordis.sexp" (asdf:system-source-directory "cl-cordis")))
    (let ((*read-eval* nil)) (read in))))

;;; ---- keys by prefix, and interception ----

(deftest "I1"
  (with-runtime (:root '(("vet/root" "root")))
    (flet ((voter (name)
             (comp name :provide (list (format nil "vet/~a" name) (format nil "x/~a" name))
                        :apply (apply-of (cordis:provide (format nil "vet/~a" name) name)
                                         (cordis:provide (format nil "x/~a" name) :no)))))
      (let ((b (cordis:use (voter "b"))) (a (cordis:use (voter "a"))))
        (cordis:settle)
        (let ((first (mapcar #'cdr (cordis:providing "vet/"))))
          (cordis:rebuild b)
          (cordis:settle)
          (let ((second (mapcar #'cdr (cordis:providing "vet/"))))
            (cordis:retire a)
            (cordis:settle)
            (let ((third (cordis:providing "vet/")))
              (ok "I1 the keys with a prefix, in the order their providers activated: the root's first; a fiber rebuilt goes last; one unloaded is gone"
                  (and (equal first '("root" "b" "a")) (equal second '("root" "a" "b"))
                       (equal third '(("vet/root" . "root") ("vet/b" . "b"))))
                  (format nil "~s ~s ~s" first second third)))))))))

(deftest "I2"
  (with-runtime ()
    (let* ((reads 0)
           (union (lambda (a b) (append a (remove-if (lambda (x) (member x a)) b))))
           (svc (comp "svc" :provide '(:fs) :apply (apply-of (cordis:merge-rule :fs union) (cordis:provide :fs t))))
           (user (cordis:make-component :name "user" :inject '(:fs) :metadata '(:fs (:read))
                                        :apply (apply-of (incf reads))))
           (s (cordis:use svc))
           (outer (cordis:use (comp "outer") :intercept '(:fs (:write))))
           (u nil))
      (cordis:settle)
      (setf u (cordis:in-fiber (outer) (cordis:use user :intercept '(:fs (:exec)))))
      (cordis:settle)
      (let* ((seen (cordis:in-fiber (u) (cordis:metadata :fs)))
             (derived (cordis:in-fiber (u)
                        (cordis:with-intercept (:fs '(:net))
                          (cordis:with-intercept (:fs '(:read :tmp))
                            (cordis:metadata :fs)))))
             (after (cordis:in-fiber (u) (cordis:metadata :fs)))
             (root (cordis:metadata :fs))
             (other (cordis:in-fiber (u)
                      (cordis:with-intercept (:fs '(:net))
                        (sb-thread:join-thread
                         (sb-thread:make-thread (lambda () (cordis:in-fiber (u) (cordis:metadata :fs))))))))
             (state (cordis:fiber-state u)))
        (ok "I2 a key's metadata is what the reading component declares merged by the key's rule with what each context adds, outermost first: the fibers from the root down, then each with-intercept; a derived context ends with its body, reaches no other thread, and reloads nothing"
            (and (equal seen '(:read :write :exec)) (equal derived '(:read :write :exec :net :tmp)) (equal after seen)
                 (null root) (equal other seen) (= reads 1) (eq state :active))
            (format nil "seen ~s derived ~s after ~s root ~s other ~s; ~d activations, ~a" seen derived after root other reads state))
        (let ((twice (handler-case (progn (cordis:merge-rule :fs union) nil)
                       (cordis:provision-conflict (e) (princ-to-string e)))))
          (cordis:retire s)
          (cordis:settle)
          (let ((without (cordis:in-fiber (u) (cordis:metadata :fs))))
            (ok "I3 a key has one merge rule, and it leaves with the fiber that gave it; a key without one keeps the innermost value"
                (and twice (search "merge rule already" twice) (equal without '(:exec)))
                (format nil "~a; ~s" twice without))))))))

(deftest "I4"
  (with-runtime ()
    (let ((boxed (comp "boxed")))
      (cordis:apply-config (list (list :id "boxed" :component boxed :intercept '(:k 1))))
      (let* ((f1 (cordis:find-fiber "boxed"))
             (one (cordis:in-fiber (f1) (cordis:metadata :k)))
             (same (cordis:apply-config (list (list :id "boxed" :component boxed :intercept '(:k 1)))))
             (changed (cordis:apply-config (list (list :id "boxed" :component boxed :intercept '(:k 2)))))
             (f2 (cordis:find-fiber "boxed"))
             (two (cordis:in-fiber (f2) (cordis:metadata :k))))
        (ok "I4 an entry of the list carries the intercept its fiber is loaded with; the same intercept changes nothing, another one loads the entry again"
            (and (eql one 1) (null same) (equal changed '(("boxed" :rebuilt))) (eql two 2) (not (eq f1 f2)))
            (format nil "~s ~s ~s ~s" one same changed two))))))

;;; ---- hooks ----

(defun wrapper (tag &key short)
  "A wrapper that marks the input with >TAG on the way in and TAG(...) on the way out; with SHORT, an input holding \"short\" never reaches INNER."
  (lambda (inner x)
    (if (and short (search "short" x))
        (format nil "~a(short:~a)" tag x)
        (format nil "~a(~a)" tag (funcall inner (format nil "~a>~a" x tag))))))

(defun wrapping (name &rest more &key (hook "h") (tag name) short &allow-other-keys)
  (declare (ignore more))
  (cordis:make-component :name name :wrap (list (cons hook (wrapper tag :short short)))))

(defun hook-h ()
  (cordis:define-hook "h" (lambda (x) (format nil "default(~a)" x))))

(deftest "H1"
  (with-runtime ()
    (hook-h)
    (let ((bare (cordis:chain "h" "x")))
      (cordis:use (wrapping "a"))
      (cordis:use (wrapping "b" :short t))
      (cordis:use (wrapping "c"))
      (cordis:settle)
      (let ((three (cordis:chain "h" "x")) (short (cordis:chain "h" "short")) (order (cordis:chain-of "h")))
        (ok "H1 a hook's chain runs the wrappers outermost first, in the order their fibers were loaded, over the default; a wrapper may answer without its inner"
            (and (equal bare "default(x)") (equal three "a(b(c(default(x>a>b>c))))")
                 (equal short "a(b(short:short>a))")

                 (equal order '(("a" :active) ("b" :active) ("c" :active))))
            (format nil "~s ~s ~s ~s" bare three short order))))))

(deftest "H2"
  (with-runtime ()
    (hook-h)
    (cordis:define-hook "g" (lambda (x) x))
    (let ((b-old (cordis:make-component :name "b" :wrap (list (cons "h" (wrapper "b")) (cons "g" (wrapper "b")))))
          (b-new (wrapping "b" :tag "B"))
          (a (wrapping "a"))
          (c (cordis:make-component :name "c" :inject '(:later) :wrap (list (cons "h" (wrapper "c"))))))
      (cordis:apply-config (list (list :id "a" :component a) (list :id "b" :component b-old) (list :id "c" :component c)))
      (cordis:settle)
      (let ((waiting (cordis:chain "h" "x")) (seen (cordis:chain-of "h")))
        (cordis:use (comp "late" :provide '(:later) :apply (apply-of (cordis:provide :later t))))
        (cordis:settle)
        (let ((all (cordis:chain "h" "x")))
          (cordis:apply-config (list (list :id "a" :component a) (list :id "b" :component b-new) (list :id "c" :component c)))
          (cordis:settle)
          (let ((replaced (cordis:chain "h" "x")) (g (cordis:chain-of "g")))
            (cordis:retire (cordis:find-fiber "b"))
            (cordis:settle)
            (let ((retired (cordis:chain "h" "x")) (left (mapcar #'first (cordis:chain-of "h"))))
              (ok "H2 a fiber that is not active is passed over and keeps its place; a new version put in by the list keeps the old one's place, and leaves the chains of the hooks it no longer wraps; a fiber taken out leaves the chain"
                  (and (equal waiting "a(b(default(x>a>b)))") (equal (third seen) '("c" :inactive))
                       (equal all "a(b(c(default(x>a>b>c))))")
                       (equal replaced "a(B(c(default(x>a>B>c))))") (null g)
                       (equal retired "a(c(default(x>a>c)))") (equal left '("a" "c")))
                  (format nil "~s ~s ~s ~s ~s ~s ~s" waiting seen all replaced g retired left)))))))))

(deftest "H3"
  (with-runtime ()
    (hook-h)
    (let* ((kept nil)
           (f (cordis:use (cordis:make-component :name "keeper"
                                                 :wrap (list (cons "h" (lambda (inner x) (setf kept inner) (funcall inner x))))))))
      (cordis:settle)
      (let* ((first (cordis:chain "h" "x"))
             (ended (handler-case (progn (funcall kept "late") :ran) (cordis:stale-inner (e) (cordis:stale-inner-reason e)))))
        (cordis:rebuild f)
        (cordis:settle)
        (let ((stale (handler-case (progn (funcall kept "later") :ran) (cordis:stale-inner (e) (cordis:stale-inner-reason e)))))
          (ok "H3 an inner called after its call ended is refused as ended; one kept from an earlier activation of its fiber, as stale"
              (and (equal first "default(x)") (eq ended :ended) (eq stale :stale))
              (format nil "~s ~s ~s" first ended stale)))))))

(deftest "H4"
  (with-runtime ()
    (hook-h)
    (flet ((refused (thunk) (handler-case (progn (funcall thunk) nil) (cordis:cordis-error (e) (list (type-of e) (princ-to-string e))))))
      (let ((unknown (refused (lambda () (cordis:use (wrapping "u" :hook "nope")))))
            (twice (refused (lambda () (cordis:use (cordis:make-component :name "t" :wrap (list (cons "h" (wrapper "t")) (cons "h" (wrapper "t2"))))))))
            (call (refused (lambda () (cordis:chain "nope" "x")))))
        (ok "H4 a component that wraps a hook nobody declared, or one hook twice, is refused before it loads; running an undeclared hook is an error"
            (and (eq (first unknown) 'cordis:unknown-hook) (search "nope" (second unknown))
                 (search "twice" (second twice)) (eq (first call) 'cordis:unknown-hook)
                 (null (cordis:fibers)) (null (cordis:chain-of "h")))
            (format nil "~s ~s ~s ~s" unknown twice call (cordis:fibers)))))))

(deftest "H5"
  (with-runtime ()
    (cordis:define-hook "who" (lambda (x) (list x (cordis:config :tag))))
    (cordis:use (cordis:make-component :name "w" :wrap (list (cons "who" (lambda (inner x) (list (cordis:config :tag) (funcall inner x))))))
                :config '(:tag :wrapper))
    (let ((caller (cordis:use (comp "caller") :config '(:tag :caller))))
      (cordis:settle)
      (let ((got (cordis:in-fiber (caller) (cordis:chain "who" 1))))
        (ok "H5 a wrapper runs as its own fiber, the default as the caller"
            (equal got '(:wrapper (1 :caller)))
            (format nil "~s" got))))))

(deftest "H6"
  (with-runtime ()
    (hook-h)
    (cordis:use (cordis:make-component
                 :name "loader"
                 :wrap (list (cons "h" (lambda (inner x)
                                         (unless (cordis:find-fiber "late")
                                           (cordis:in-fiber (nil) (cordis:use (wrapping "late")))
                                           (cordis:settle))
                                         (format nil "L(~a)" (funcall inner x)))))))
    (cordis:use (wrapping "b"))
    (cordis:settle)
    (let* ((during (cordis:chain "h" "x")) (after (cordis:chain "h" "x")))
      (ok "H6 a call runs the chain it found when it started: a wrapper loaded during the call runs from the next call on"
          (and (equal during "L(b(default(x>b)))") (equal after "L(b(late(default(x>b>late))))"))
          (format nil "~s ~s" during after)))))

(deftest "H7"
  (with-runtime ()
    (hook-h)
    (let ((path (put "wrap-file.lisp"
                     (format nil "(in-package #:cordis-sandbox)~%(cordis:component :wrap ((\"h\" . file-wrap)))~%(defun file-wrap (inner x) (format nil \"file(~~a)\" (funcall inner x)))~%"))))
      (cordis:apply-config (list (list :id "wrap-file" :file path)))
      (cordis:settle)
      (let ((got (cordis:chain "h" "x")))
        (cordis:apply-config '())
        (cordis:settle)
        (ok "H7 a component file names its wrappers in its header, functions its body defines; they leave with it"
            (and (equal got "file(default(x))") (equal (cordis:chain "h" "x") "default(x)") (not (sandbox-fbound "file-wrap")))
            (format nil "~s ~s" got (cordis:chain "h" "x")))))))

(defun hooks-case-file ()
  (with-open-file (in (merge-pathnames "test/cases/cordis-hooks.sexp" (asdf:system-source-directory "cl-cordis")))
    (let ((*read-eval* nil)) (read in))))

(defun z2-link (l) (if (eq (first l) :default) "default" (second l)))
(defun z2-triple (tok)
  (and tok (list (cl-cordis.core.hooks:activation-of tok) (cl-cordis.core.hooks:call-of tok) (cl-cordis.core.hooks:position-of tok))))
(defun z2-answer (r)
  (and r (if (eq (first r) :resolved)
             (list "resolved" (z2-link (second r)))
             (list (string-downcase (symbol-name (first r)))))))

(defun z2-run (ops)
  "Replay OPS on new chains: the first operation whose answer differs from bendcord's, with what came, or nil."
  (let ((c (cordis::make-chains)) (snaps (make-array 0 :adjustable t :fill-pointer 0)) (tokens (make-hash-table)))
    (flet ((token (ref) (if (consp ref) (apply #'cl-cordis.core.hooks::make-token (rest ref)) (gethash ref tokens))))
      (dolist (op ops nil)
        (multiple-value-bind (got want)
            (ecase (first op)
              (:add (destructuring-bind (hook id want) (rest op) (values (and (cordis::chains-add c hook id) t) want)))
              (:remove (cordis::chains-remove c (second op)) (values t t))
              (:rejoin (cordis::chains-rejoin c (second op) (third op)) (values t t))
              (:admits (destructuring-bind (id hooks replacing want) (rest op)
                         (values (and (cordis::chains-admits c id hooks replacing) t) want)))
              (:activate (cordis::chains-activate c (second op)) (values t t))
              (:snapshot (destructuring-bind (k hook active want) (rest op)
                           (let ((snap (cordis::chains-snapshot c hook (lambda (id) (member id active :test #'equal)))))
                             (values (and (= k (vector-push-extend snap snaps))
                                          (loop for i below 6 collect (z2-link (cordis::chains-step c snap i))))
                                     want))))
              (:open (destructuring-bind (j id k position want) (rest op)
                       (let ((tok (cordis::chains-open c id (aref snaps k) position)))
                         (when j (setf (gethash j tokens) tok))
                         (values (z2-triple tok) want))))
              (:resolve (destructuring-bind (id ref want) (rest op)
                          (values (z2-answer (cordis::chains-resolve c id (token ref))) want)))
              (:end (cordis::chains-end c (second op) (token (third op))) (values t t)))
          (unless (equal got want) (return (list op got))))))))

(deftest "Z2"
  (let* ((sequences (hooks-case-file))
         (bad (loop for s in sequences for d = (z2-run s) when d collect d)))
    (ok (format nil "Z2 the hook chains answer as bendcord's TypeScript shell on its core: ~d sequences, ~d operations"
                (length sequences) (reduce #'+ sequences :key #'length))
        (null bad)
        (format nil "~d differ; first: ~s" (length bad) (first bad)))))

(deftest "Z1"
  (let ((n 0) (bad '()))
    (dolist (c (case-file))
      (incf n)
      (let ((got (ecase (first c)
                   (:check (cordis::core-check (second c) (third c)))
                   (:plan (multiple-value-list (cordis::core-plan (second c) (third c))))
                   (:cascade (cordis::core-cascade (second c) (third c)))
                   (:undo (cordis::core-undo (second c)))))
            (want (ecase (first c)
                    (:check (fourth c))
                    (:plan (list (fourth c) (fifth c)))
                    ((:cascade :undo) (car (last c))))))
        (unless (equal got want) (push (list c got) bad))))
    (ok (format nil "Z1 check, plan, cascade and undo answer as bendcord's TypeScript shell on its cores, ~d cases" n)
        (and (> n 600) (null bad))
        (format nil "~d differ; first ~s" (length bad) (first (last bad))))))

;;; ---- a new image ----

(defun fresh ()
  "In a new image: load the list the checks ended E5 with, and write what the image holds."
  (cordis:start)
  (unwind-protect
       (progn
         (cordis:apply-config (with-open-file (in (concatenate 'string *dir* "final.specs")) (read in)))
         (cordis:settle)
         (write-lines "fresh.image" (cordis:image-lines (cordis:image :packages *packages*))))
    (cordis:stop))
  t)

(defun run-all ()
  (let ((only (sb-ext:posix-getenv "ONLY"))
        (threads (length (sb-thread:list-all-threads))))
    (dolist (test (reverse *tests*))
      (when (or (null only) (string= only "") (eql 0 (search only (car test))))
        (let* ((done (list nil))
               (watchdog (watch (car test) done)))
          (handler-case (funcall (cdr test))
            (error (e)
              (when (cordis:running-p) (ignore-errors (cordis:stop)))
              (ok (format nil "~a ended with an error" (car test)) nil (princ-to-string e))))
          (setf (car done) t)
          (sb-thread:join-thread watchdog :default nil))))
    (wait-for (lambda () (<= (length (sb-thread:list-all-threads)) threads)) 3)
    (ok "no check left a thread behind" (<= (length (sb-thread:list-all-threads)) threads)
        (format nil "~s" (mapcar #'sb-thread:thread-name (sb-thread:list-all-threads))))
    (format t "~%~d passed, ~d failed~%" *pass* *fail*)
    (zerop *fail*)))
