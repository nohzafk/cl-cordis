#!/usr/bin/env bash
# The checks of cl-cordis, with the system loaded through ASDF. -v prints the
# measured detail of every check.
#   SBCL          path to sbcl when none is on PATH
#   CL_SCOPE_DIR  path to a cl-scope checkout (default: ../cl-scope if present)
#   QLOT_SETUP    path to a .qlot/setup.lisp (default: .qlot/setup.lisp if present)
#   MUTANT=file   loads that file as source over the compiled system (mutants.sh)
#   ONLY=prefix   runs the checks whose name starts with it
#   FIRST_FAIL=1  stops at the first failed check
#   CHECK_LIMIT   seconds a check may take before failing (default 5)
#   1. the checks in one image (test.lisp)
#   2. K1: a second, new image loads the list the first ended with, and what
#      the two hold is compared
set -u
cd "$(dirname "$0")"
SBCL=${SBCL:-$(command -v sbcl || ls -d /nix/store/*-sbcl-*/bin/sbcl 2>/dev/null | sort | tail -1)}
[ -x "$SBCL" ] || { echo "no sbcl: set SBCL"; exit 1; }

D=$(mktemp -d)
D=$(cd "$D" && pwd -P)
trap 'rm -rf "$D"' EXIT
export DIR="$D"

# Resolve how cl-scope is made visible to ASDF.
SCOPE_ARGS=()
if [ -n "${CL_SCOPE_DIR:-}" ] && [ -f "$CL_SCOPE_DIR/cl-scope.asd" ]; then
  SCOPE_ARGS=(--eval "(asdf:load-asd #P\"$(cd "$CL_SCOPE_DIR" && pwd -P)/cl-scope.asd\")")
elif [ -n "${QLOT_SETUP:-}" ] && [ -f "$QLOT_SETUP" ]; then
  SCOPE_ARGS=(--load "$QLOT_SETUP" --eval '(let ((*error-output* (make-broadcast-stream))) (ql:quickload "cl-scope" :silent t))')
elif [ -f ".qlot/setup.lisp" ]; then
  SCOPE_ARGS=(--load ".qlot/setup.lisp" --eval '(let ((*error-output* (make-broadcast-stream))) (ql:quickload "cl-scope" :silent t))')
elif [ -f "../cl-scope/cl-scope.asd" ]; then
  SCOPE_ARGS=(--eval "(asdf:load-asd #P\"$(cd ../cl-scope && pwd -P)/cl-scope.asd\")")
fi

failed=0
image() {
  "$SBCL" --noinform --non-interactive --no-sysinit --no-userinit \
    --eval '(require :asdf)' \
    "${SCOPE_ARGS[@]}" \
    --eval '(asdf:load-asd (merge-pathnames "cl-cordis.asd" (uiop:getcwd)))' \
    --eval '(let ((*error-output* (make-broadcast-stream))) (asdf:load-system "cl-cordis/test"))' \
    "$@"
}
image ${MUTANT:+--load "$MUTANT"} \
  --eval '(sb-ext:exit :code (if (cl-cordis/test:run-all) 0 1) :abort t)' "$@" || failed=1

[ $failed -ne 0 ] && [ -n "${FIRST_FAIL:-}" ] && exit 1
if [ -z "${ONLY:-}" ]; then
  image ${MUTANT:+--load "$MUTANT"} \
    --eval '(sb-ext:exit :code (if (cl-cordis/test:fresh) 0 1) :abort t)' > "$D/fresh.out" 2>&1
  if [ -s "$D/live.image" ] && cmp -s "$D/live.image" "$D/fresh.image"; then
    echo "ok   K1 a new image that loads the last list alone holds what the image with the history holds"
    [ "${1:-}" = "-v" ] && sed 's/^/       /' "$D/live.image"
  else
    echo "FAIL K1 a new image that loads the last list alone holds what the image with the history holds"
    diff "$D/live.image" "$D/fresh.image" 2>&1 | head -20; tail -5 "$D/fresh.out"
    failed=1
  fi
fi
exit $failed
