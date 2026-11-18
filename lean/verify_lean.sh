#!/usr/bin/env bash
# Verify the six Lean 4 files of this archive.
# For each file: no forbidden construct (sorry, admit, native_decide, axiom or opaque
# declarations, unsafe code, implemented_by/extern, debug options such as skipKernelTC),
# compilation with exit code 0, and the printed axioms equal to expected/salida_<file>.txt.
# Compiler outputs are written to a temporary directory, not to the archive.
# Usage: ./verify_lean.sh            (uses `lean` from PATH, e.g. installed with elan)
#        LEAN=/path/to/lean ./verify_lean.sh
set -u
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
if ! version=$("$LEAN" --version 2>/dev/null); then
  echo "lean not found. Install elan (https://github.com/leanprover/elan); the file lean-toolchain selects Lean 4.24.0." >&2
  exit 2
fi
echo "$version"
case "$version" in
  *"version 4.24.0"*) ;;
  *) echo "WARNING: these files were checked with Lean 4.24.0; another version may print different output." ;;
esac
status=0
OUT=$(mktemp -d "${TMPDIR:-/tmp}/verify_lean.XXXXXX")
for f in IntentoSu UnificacionCat PistasUnificacion FiltracionCociente ViaFutura GaussConexion; do
  if grep -nE '\bsorry\b|\badmit\b|native_decide|^[[:space:]]*((private|protected|noncomputable)[[:space:]]+)*(axiom|opaque)[[:space:]]|skipKernelTC|debug\.|\bunsafe\b|implemented_by|@\[extern' "$f.lean"; then
    echo "FAIL  $f.lean: forbidden construct"; status=1; continue
  fi
  out=$("$LEAN" "$f.lean" 2>&1); rc=$?
  printf '%s\nexit %s\n' "$out" "$rc" > "$OUT/out_$f.txt"
  if [ "$rc" -ne 0 ]; then
    echo "FAIL  $f.lean: exit code $rc (see $OUT/out_$f.txt)"; status=1; continue
  fi
  if diff -q "$OUT/out_$f.txt" "expected/salida_$f.txt" > /dev/null; then
    echo "OK    $f.lean: exit 0, axioms as expected"
  else
    echo "DIFF  $f.lean: output differs from expected/salida_$f.txt"; diff "$OUT/out_$f.txt" "expected/salida_$f.txt"; status=1
  fi
done
echo "compiler outputs: $OUT"
if [ "$status" -eq 0 ]; then echo "ALL LEAN CHECKS PASSED"; else echo "SOME LEAN CHECKS FAILED"; fi
exit $status
