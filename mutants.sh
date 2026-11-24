#!/usr/bin/env bash
# Do the checks test cl-cordis? Each mutant is cordis.lisp with one behaviour
# taken out, loaded as source over the compiled system and run against the
# checks. A mutant is caught when a check fails, or a check runs past its
# CHECK_LIMIT, or the run does not end within LIMIT.
#   ./mutants.sh          every mutant, JOBS at a time (default: every processor)
#   ./mutants.sh WORDS    the mutants whose description holds one of the words
# A run stops at its first failed check; ALL=1 runs every check and names all that fail.
# Each line ends with the seconds its run took.
set -u
set -m   # each run is a process group of its own, so the limit can end all of it
SELF=$(cd "$(dirname "$0")" && pwd -P)/$(basename "$0")   # it runs itself again after the cd
cd "$(dirname "$0")"
LIMIT=${LIMIT:-40}
WORDS="$*"
[ -n "${ALL:-}" ] || export FIRST_FAIL=1

# Without ONE this is the driver: it counts the mutants, then runs itself once for each.
if [ -z "${ONE:-}" ]; then
  # The runs share the compiled system. It is compiled here, once: two runs that both find a
  # compiled file out of date write it at the same time, and one of them loads half of it.
  MUTANT=/dev/null ONLY=no-check ./check.sh > /dev/null 2>&1 || { echo "cl-cordis does not compile; ./check.sh says why"; exit 1; }
  count=$(ONE=count "$SELF" "$@")
  out=$(seq 1 "$count" | xargs -P "${JOBS:-$(sysctl -n hw.ncpu 2>/dev/null || nproc)}" -I{} env ONE={} "$SELF" "$@")
  echo "$out"
  if echo "$out" | grep -q '^\(SURVIVED\|BROKEN\)'; then exit 1; fi
  [ "$(echo "$out" | grep -c '^caught')" -eq "$count" ] || { echo "$count mutants, not as many lines"; exit 1; }
  echo "every mutant caught ($count)"
  exit 0
fi

D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
survived=0
n=0

# mutant <what it takes out> <text of cordis.lisp> <what replaces it>
mutant() {
  if [ $# -gt 3 ]; then echo "usage"; exit 2; fi
  if [ -n "$WORDS" ]; then
    hit=; for w in $WORDS; do case "$1" in *"$w"*) hit=1;; esac; done
    [ -n "$hit" ] || return
  fi
  n=$((n + 1))
  [ "$ONE" = "$n" ] || return
  SECONDS=0
  cp cordis.lisp "$D/cordis.lisp"
  OLD="$2" NEW="$3" perl -0pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/' "$D/cordis.lisp"
  if cmp -s cordis.lisp "$D/cordis.lisp"; then
    echo "BROKEN   $1: the text to replace is not in cordis.lisp"; survived=1; return
  fi
  # SBCL handles SIGALRM itself, so the limit is a watcher that kills the run.
  MUTANT="$D/cordis.lisp" TMPDIR="$D" ./check.sh > "$D/out" 2>&1 &
  run=$!
  (sleep "$LIMIT"; kill -9 -- -$run 2>/dev/null) &
  watch=$!
  { wait $run; code=$?; } 2>/dev/null
  kill -9 -- -$watch 2>/dev/null; wait $watch 2>/dev/null
  failed=$(sed -n 's/^FAIL \([A-Z][A-Z]*[0-9][0-9]*[a-z]*\).*/\1/p' "$D/out" | tr '\n' ' ')
  late=$(grep -q 'did not end in .* (CHECK_LIMIT)' "$D/out" && echo " (past CHECK_LIMIT)")
  if [ $code -eq 0 ]; then echo "SURVIVED $1  [${SECONDS}s]"; survived=1
  elif [ $code -eq 137 ]; then echo "caught   $1: the run did not end in $LIMIT s  [${SECONDS}s]"
  elif [ -n "$failed" ]; then echo "caught   $1: $failed$late [${SECONDS}s]"
  else echo "BROKEN   $1: the run ended with $code and no failed check  [${SECONDS}s]"; tail -5 "$D/out"; survived=1; fi
}

mutant "inverses run oldest first" \
  "(dolist (n (core-undo entries))" \
  "(dolist (n (reverse (core-undo entries)))"
mutant "an inverse that fails stops the ones behind it" \
  "(handler-case (let ((*fiber* owner)) (funcall thunk))
          (error (e) (note-failure rt owner e)))" \
  "(let ((*fiber* owner)) (funcall thunk))"
mutant "an inverse runs as the root, not as its fiber" \
  "(let ((*fiber* owner)) (funcall thunk))" \
  "(funcall thunk)"
mutant "an effect is made for a fiber that is not installed" \
  "(unless (locked (rt) (installed-p rt fiber))
      (fail 'cordis-error \"~a is not installed: the effect would belong to nothing that can undo it\" (fiber-id fiber)))" \
  ""
mutant "a child's ledger is not undone with its parent's" \
  "(list :c n (take child))" \
  "(list :e n)"
mutant "what a fiber read is gone before its inverses run" \
  "(undo-ledger rt fiber)
  (drop-bindings rt fiber)
  ;; every key" \
  "(setf (fiber-committed fiber) '())
  (undo-ledger rt fiber)
  (drop-bindings rt fiber)
  ;; every key"
mutant "the cascade is not asked: nothing that reads a key restarts" \
  "(set (union (core-cascade (mapcar #'comp-of live) keys) leaving))" \
  "(set leaving)"
mutant "fibers stop oldest first" \
  "(dolist (f (reverse live))
      (when (and (member f stop)" \
  "(dolist (f live)
      (when (and (member f stop)"
mutant "a fiber's children are not stopped with it" \
  "(kids (remove-if-not (lambda (f) (intersection (ancestors f) set)) (locked (rt) (runtime-loaded rt))))" \
  "(kids '())"
mutant "the plan is not asked: fibers activate in load order" \
  "(find-if-not #'fiber-live (core-plan (runtime-root-keys rt) (mapcar #'comp-of candidates)))" \
  "(find-if-not #'fiber-live candidates)"
mutant "a failed fiber activates again when the plan runs" \
  "(let ((candidates (remove-if #'fiber-error (runtime-loaded rt))))" \
  "(let ((candidates (runtime-loaded rt)))"
mutant "a load is not checked" \
  "(let ((err (core-check (runtime-root-keys rt)
" \
  "(let ((err nil) (unused (list (runtime-root-keys rt)
"
mutant "the root sets a key it was not started with" \
  "(unless (member key (runtime-root-keys rt) :test #'equal)
      (refuse 'not-root" \
  "(unless t
      (refuse 'not-root"
mutant "an operation that waits behind a parked one is run after the answer, not refused" \
  "          (unless (or (op-done op) (op-started op))
            (setf (runtime-ops rt) (remove op (runtime-ops rt)))" \
  "          (unless t
            (setf (runtime-ops rt) (remove op (runtime-ops rt)))"
mutant "a key is set without being declared" \
  "(unless (member key (component-provide (fiber-component fiber)) :test #'equal)
                    (refuse 'undeclared-access" \
  "(unless t
                    (refuse 'undeclared-access"
mutant "a key is read without being declared" \
  "(refuse 'undeclared-access \"~a reads ~s, which it does not declare\" (fiber-id (here rt)) key))" \
  "(return (let ((b (live-binding rt key))) (and b (binding-value b)))))"
mutant "a key set again by an active fiber restarts nothing" \
  "(when (fiber-active fiber)
                    (pushnew key (runtime-dirty rt) :test #'equal)
                    t)" \
  "(when (fiber-active fiber)
                    t)"
mutant "a set returns before what reads the key has restarted" \
  "(when (and active (not *op*))" \
  "(when nil"
mutant "an apply that leaves a provided key unset activates" \
  "(when unset
                            (fail 'cordis-error" \
  "(when nil
                            (fail 'cordis-error"
mutant "ABANDON leaves the component not failed" \
  "(locked (rt) (setf (fiber-error fiber) why))" \
  "nil"
mutant "RETRY undoes nothing" \
  "(undo-ledger rt fiber)
                      (drop-bindings rt fiber)
                      (commit))" \
  "(commit))"
mutant "REBUILD leaves the fiber as it is" \
  "(reconcile rt :restart (and (fiber-live fiber) (list fiber)))" \
  "(reconcile rt)"
mutant "a fiber taken out stays loaded" \
  "(unless (fiber-retired f) (leave rt f))" \
  "nil"
mutant "STOP takes nothing out" \
  "(reconcile rt :removed (locked (rt) (copy-list (runtime-loaded rt))))
                               (undo-ledger rt (runtime-root rt))" \
  "nil"
mutant "a component's thread is not cancelled" \
  "(sc:cancel-scope scope :unloaded)
           (sb-thread:join-thread" \
  "(sb-thread:join-thread"
mutant "a definition is not an effect" \
  "(define-place (list :function name) (lambda () (eval form)) source))" \
  "(eval form))"
mutant "taking a definition out puts back what the image had, whatever is left" \
  "(restore-place place (if (cdr cell) (layer-value (second cell)) (car cell)))" \
  "(restore-place place (car cell))"
mutant "a variable a component defines stays" \
  "(define-place (list :variable name) (lambda () (eval form)) source))" \
  "(eval form))"
mutant "a variable a fiber sets again keeps its earlier value too" \
  "(and top (eq (first place) :variable) (eq (layer-fiber top) fiber))" \
  "nil"
mutant "a function a component binds stays" \
  "(lambda () (setf (fdefinition name) function))
                                            source))))" \
  "(lambda () (setf (fdefinition name) function))
                                            source)))
  (lambda () nil))"
mutant "an amended config is not what the next rebuild is given" \
  "(when (entry-fiber entry) (setf (fiber-config (entry-fiber entry)) config))" \
  "nil"
mutant "an entry that did not change is rebuilt" \
  "(unless (and old (equal print (entry-print old)))" \
  "(unless nil"
mutant "a changed file is not seen" \
  ":fingerprint (md5 text)" \
  ":fingerprint path"
mutant "keys with a prefix come in the order their fibers were loaded" \
  "(loop for f in (runtime-live rt)
               when (fiber-active f)" \
  "(loop for f in (runtime-loaded rt)
               when (fiber-active f)"
mutant "metadata leaves out what the component declares" \
  "(add (component-metadata (fiber-component fiber)))" \
  "nil"
mutant "metadata leaves out what the fibers' contexts add" \
  "(unless (root-p rt f) (add (fiber-intercept f)))" \
  "nil"
mutant "metadata merges the contexts innermost first" \
  "(dolist (f (reverse (cons fiber (ancestors fiber))))" \
  "(dolist (f (cons fiber (ancestors fiber)))"
mutant "with-intercept adds nothing" \
  "(append *intercepts* (list layer))" \
  "*intercepts*"
mutant "a merge rule stays after its fiber leaves" \
  "(lambda () (locked (rt) (remhash key (runtime-merges rt))))" \
  "(lambda () nil)"
mutant "a key takes a second merge rule" \
  "(if (gethash key (runtime-merges rt))
                    (setf taken t)" \
  "(if nil
                    (setf taken t)"
mutant "a fiber is loaded without its intercept" \
  ":config config :parent parent :intercept intercept)" \
  ":config config :parent parent)"
mutant "an entry's intercept is not part of what tells it changed" \
  "(getf spec :config) disabled (getf spec :intercept))" \
  "(getf spec :config) disabled)"
mutant "an entry left out of the list stays" \
  "(take-out entry)
            (push (list (entry-id entry) :removed) done)" \
  "(push (list (entry-id entry) :removed) done)"

mutant "a fiber's wrapper is added at the front of the chain" \
  "(dolist (hook hooks) (chains-add (runtime-chains rt) hook id))" \
  "(dolist (hook hooks) (setf (gethash hook (chains-hooks (runtime-chains rt))) (cons (cl-cordis.core.hooks::make-entry (chains-nat (runtime-chains rt) id)) (chains-of (runtime-chains rt) hook))))"
mutant "a new version put in by the list goes to the end of the chain" \
  "(if replacing
                       (chains-rejoin (runtime-chains rt) id hooks)" \
  "(if nil
                       (chains-rejoin (runtime-chains rt) id hooks)"
mutant "a fiber the list puts a new version of loses its place when it is taken out" \
  "(unless (member (fiber-id fiber) (runtime-replacing rt) :test #'equal)
      (chains-remove" \
  "(unless nil
      (chains-remove"
mutant "a fiber taken out keeps its wrappers" \
  "(unless (member (fiber-id fiber) (runtime-replacing rt) :test #'equal)
      (chains-remove (runtime-chains rt) (fiber-id fiber)))" \
  ""
mutant "a fiber that is not active is not passed over" \
  "(lambda (id) (let ((f (loaded-fiber rt id))) (and f (fiber-active f))))" \
  "(lambda (id) (loaded-fiber rt id))"
mutant "a call runs the chain as it is when each link runs, not as it was when the call started" \
  "(:resolved (run-link rt hook snap (second r)" \
  "(:resolved (run-link rt hook (chains-snapshot (runtime-chains rt) hook (lambda (id) (let ((f (loaded-fiber rt id))) (and f (fiber-active f))))) (second r)"
mutant "a call's token is never ended" \
  "(locked (rt) (chains-end (runtime-chains rt) id token))))))" \
  "nil))))"
mutant "an activation keeps the calls of the one before" \
  "(chains-activate (runtime-chains rt) (fiber-id fiber))
      (changed rt))" \
  "(unless (gethash (fiber-id fiber) (chains-calls (runtime-chains rt))) (chains-activate (runtime-chains rt) (fiber-id fiber)))
      (changed rt))"
mutant "a wrapper of an undeclared hook is let in" \
  "(when unknown (refuse 'unknown-hook" \
  "(when nil (refuse 'unknown-hook"
mutant "a component that wraps a hook twice is let in" \
  "(unless (chains-admits (runtime-chains rt) id hooks replacing)" \
  "(unless t"
mutant "a wrapper runs as the caller" \
  "(let ((*fiber* fiber))
               (funcall wrapper" \
  "(let ()
               (funcall wrapper"
mutant "the default runs as the innermost wrapper" \
  "(let ((*fiber* caller)) (funcall default input))" \
  "(funcall default input)"
mutant "a file component's wrappers are not read from its header" \
  ":wrap (getf header :wrap)" \
  ""

# ---- observing ----
mutant "a component's set tells no watcher" \
  "(setf (gethash key (runtime-store rt)) (make-binding :key key :value value :fiber fiber))
                  (wrote rt key)" \
  "(setf (gethash key (runtime-store rt)) (make-binding :key key :value value :fiber fiber))"
mutant "the root's set tells no watcher" \
  "(make-binding :key key :value value :fiber (runtime-root rt)))
    (wrote rt key)" \
  "(make-binding :key key :value value :fiber (runtime-root rt)))"
mutant "a stop tells the watchers nothing of the keys it clears" \
  "(dolist (key (component-provide (fiber-component fiber))) (wrote rt key))" \
  "nil"
mutant "a stop tells the watchers of its keys before they are cleared" \
  "(drop-bindings rt fiber)
  ;; every key it declares is cleared, one it never set too
  (dolist (key (component-provide (fiber-component fiber))) (wrote rt key))" \
  "(dolist (key (component-provide (fiber-component fiber))) (wrote rt key))
  (drop-bindings rt fiber)"
mutant "a stop tells the watchers of its keys newest first" \
  "(dolist (key (component-provide (fiber-component fiber))) (wrote rt key))" \
  "(dolist (key (reverse (component-provide (fiber-component fiber)))) (wrote rt key))"
mutant "removing a watcher removes every registration of its listener" \
  "(remove own (runtime-watchers rt) :test #'eq)" \
  "(remove (cdr own) (runtime-watchers rt) :key #'cdr)"
mutant "a removed watcher is still called" \
  "(locked (rt) (setf (runtime-watchers rt) (remove own (runtime-watchers rt) :test #'eq)))
      nil" \
  "nil"

mutant "changes does not tell what the key holds now" \
  "(locked (rt)
        (tell)
        (watch" \
  "(locked (rt)
        (watch"
mutant "changes tells of a write to any key" \
  "(when (equal name key) (tell))" \
  "(progn name (tell))"
mutant "changes tells only what an active component set" \
  "(multiple-value-bind (b present) (gethash key (runtime-store rt))
               (funcall listener (and present (binding-value b)) present))" \
  "(multiple-value-call listener (value key))"
mutant "status calls a component that is not active failed" \
  "((fiber-active fiber) :active)
              (t :blocked)" \
  "((fiber-active fiber) :active)
              (t :failed)"
mutant "status of a failed component is blocked" \
  "((fiber-error fiber) (values :failed (fiber-error fiber)))
              ((fiber-active fiber) :active)" \
  "((fiber-active fiber) :active)"
mutant "status of an id that is not loaded is blocked" \
  "(cond ((null fiber) nil)
              ((fiber-error fiber) (values" \
  "(cond ((null fiber) :blocked)
              ((fiber-error fiber) (values"
mutant "active lists the loaded ids in load order" \
  "(loop for fiber in (runtime-live rt)
            when (and (fiber-active fiber)" \
  "(loop for fiber in (runtime-loaded rt)
            when (and (fiber-active fiber)"
mutant "faults are newest first" \
  "(locked (rt) (reverse (runtime-faults rt)))" \
  "(locked (rt) (copy-list (runtime-faults rt)))"
mutant "a failed inverse is no fault" \
  "(push (cons (fiber-id fiber) text) (runtime-faults rt))" \
  "nil"

[ "$ONE" = count ] && echo "$n"
exit $survived
