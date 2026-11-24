#!/usr/bin/env bash
# Check every Bend core's PROOF.bend with Bend's kernel, then emit the 9 Common
# Lisp files under cores/ in private cl-cordis.* packages using bend-emit-cl.
#
# Normal Lisp users do not need to run this script: the emitted cores/*.lisp are
# checked into git. Run it only when modifying bend/ or upgrading bend-emit-cl.
#
#   cores/build.sh           check proofs, emit cores/*.lisp, write cores/SOURCES
#   cores/build.sh --check   rebuild into a temp dir and verify committed files match
#
# Environment overrides:
#   BEND          path to bend binary (default: ~/projects/.toolchains/bend-<V>/bin/bend or bend on PATH)
#   BEND_EMIT_CL  path to a bend-emit-cl checkout (default: ../bendcord.cl/vendor/bend-emit-cl or ../bend-emit-cl)
#   JOBS          parallel proof checks (default: 6)
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
BEND_DIR="$ROOT/bend"
V=$(cat "$BEND_DIR/BEND_VERSION")

BEND=${BEND:-$(
  if [ -x "$HOME/projects/.toolchains/bend-$V/bin/bend" ]; then
    echo "$HOME/projects/.toolchains/bend-$V/bin/bend"
  else
    command -v bend || true
  fi
)}
[ -n "$BEND" ] && [ -x "$BEND" ] || { echo "no bend binary found for $V: set BEND"; exit 1; }

EMIT=${BEND_EMIT_CL:-$(
  for d in "$ROOT/../bendcord.cl/vendor/bend-emit-cl" "$ROOT/../bend-emit-cl"; do
    if [ -f "$d/src/emit-cl.ts" ] && [ -f "$d/BEND_VERSION" ] && [ "$(cat "$d/BEND_VERSION")" = "$V" ]; then
      echo "$d"; break
    fi
  done
)}
[ -n "$EMIT" ] && [ -f "$EMIT/src/emit-cl.ts" ] || { echo "no bend-emit-cl checkout for Bend $V: set BEND_EMIT_CL"; exit 1; }
EMIT=$(cd "$EMIT" && pwd)
[ "$(cat "$EMIT/BEND_VERSION")" = "$V" ] || { echo "bend-emit-cl is for Bend $(cat "$EMIT/BEND_VERSION"), cl-cordis requires $V"; exit 1; }

T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
OUT="$HERE"
if [ "${1:-}" = "--check" ]; then OUT="$T/out"; fi
mkdir -p "$OUT" "$T/verdict"

CORES="keys comp cascade check hooks plan undo"

# 1. Verify every PROOF.bend through Bend's kernel.
export BEND BEND_DIR T
printf '%s\n' $CORES | xargs -P "${JOBS:-6}" -n 1 sh -c '
  dir="$1"
  if [ -f "$BEND_DIR/$dir/PROOF.bend" ]; then
    verdict=$(cd "$BEND_DIR/$dir" && BEND_NO_TELEMETRY=1 "$BEND" PROOF.bend --verdict 2>&1 | grep -E "^(ALL|SOME) PROOFS" || true)
  else
    verdict="no PROOF.bend: its laws are in the cores that import it"
  fi
  echo "${verdict:-no verdict}" > "$T/verdict/$dir"
' sh

bad=0
for c in $CORES; do
  v=$(cat "$T/verdict/$c")
  case "$v" in
    "ALL PROOFS CHECK"* | "no PROOF.bend"*) ;;
    *) echo "bend/$c: proofs failed: $v"; bad=1 ;;
  esac
done
[ "$bad" = 0 ] || exit 1

# 2. Emit all 7 cores + private runtime + private Base as one image.
cat > "$T/IMAGE.json" <<EOF
{
  "runtime": "cl-cordis.runtime",
  "base": { "package": "cl-cordis.base", "file": "base.lisp" },
  "modules": [
    { "id": "keys",    "package": "cl-cordis.core.keys",    "source": "$BEND_DIR/keys/core.bend" },
    { "id": "comp",    "package": "cl-cordis.core.comp",    "source": "$BEND_DIR/comp/core.bend" },
    { "id": "cascade", "package": "cl-cordis.core.cascade", "source": "$BEND_DIR/cascade/core.bend" },
    { "id": "check",   "package": "cl-cordis.core.check",   "source": "$BEND_DIR/check/core.bend" },
    { "id": "hooks",   "package": "cl-cordis.core.hooks",   "source": "$BEND_DIR/hooks/core.bend" },
    { "id": "plan",    "package": "cl-cordis.core.plan",    "source": "$BEND_DIR/plan/core.bend" },
    { "id": "undo",    "package": "cl-cordis.core.undo",    "source": "$BEND_DIR/undo/core.bend" }
  ]
}
EOF

bun "$EMIT/src/emit-cl.ts" --image "$T/IMAGE.json" "$OUT" > "$T/emit.log" 2>&1 || { cat "$T/emit.log"; exit 1; }
# Remove machine-local absolute-path maps/metadata and normalize origin comments.
rm -f "$OUT"/*.map.json "$OUT/NAMES.json"
ROOT_PREFIX="$ROOT/" EMIT_BASE="$EMIT/vendor/bend/bend2/" perl -pi -e '
  s/\Q$ENV{ROOT_PREFIX}\E//g;
  s/\Q$ENV{EMIT_BASE}\E/Base\//g;
' "$OUT"/*.lisp

md5sum_of() {
  if command -v md5 >/dev/null 2>&1; then md5 -q "$1"
  else md5sum "$1" | awk '{print $1}'; fi
}

{
  echo "bend $V"
  echo "emitter bend-emit-cl $(git -C "$EMIT" rev-parse --short HEAD 2>/dev/null || echo unknown), Bend source $(git -C "$EMIT/vendor/bend" rev-parse --short HEAD 2>/dev/null || echo unknown)"
  echo "runtime.lisp: package cl-cordis.runtime"
  echo "base.lisp: package cl-cordis.base"
  for c in $CORES; do
    echo "$c.lisp: package cl-cordis.core.$c, from bend/$c"
    if [ -f "$BEND_DIR/$c/LAWS.bend" ]; then
      echo "  $(cat "$T/verdict/$c"); defs in LAWS.bend: $(grep -c '^def ' "$BEND_DIR/$c/LAWS.bend")"
    else
      echo "  $(cat "$T/verdict/$c")"
    fi
    for g in core.bend FACTS.bend LAWS.bend PROOF.bend; do
      [ -f "$BEND_DIR/$c/$g" ] && echo "  $(md5sum_of "$BEND_DIR/$c/$g") $g"
    done
  done
} > "$OUT/SOURCES"

if [ "${1:-}" = "--check" ]; then
  for f in runtime.lisp base.lisp keys.lisp comp.lisp cascade.lisp check.lisp hooks.lisp plan.lisp undo.lisp SOURCES; do
    cmp -s "$OUT/$f" "$HERE/$f" || { echo "cores/$f differs from fresh build"; exit 1; }
  done
  echo "cores/ matches fresh Bend $V build"
else
  echo "7 cores, runtime, and base emitted to $OUT (Bend $V)"
fi
