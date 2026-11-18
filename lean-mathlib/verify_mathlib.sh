#!/usr/bin/env bash
# Verify the Lean 4 + Mathlib formalization of the analytic results of the paper
# (Lemma J, the min-cut sandwich and the proposition on monotonicity under scaling),
# with the bridge between the two developments, the interval lemma and non-vacuity examples.
# For each file: no forbidden construct (sorry, admit, native_decide, axiom or opaque
# declarations, unsafe code, implemented_by/extern, debug options such as skipKernelTC),
# compilation with exit code 0, and the printed axioms equal to expected/salida_<file>.txt.
# The first run clones Mathlib and downloads its prebuilt cache with `lake exe cache get`
# (about 1 GB in all; about 7 GB of disk with the build).
# Usage: bash verify_mathlib.sh      (needs `lake`, installed with elan; lean-toolchain selects
#                                     Lean 4.24.0 and lake-manifest.json pins Mathlib v4.24.0)
set -u
cd "$(dirname "$0")"
command -v lake > /dev/null 2>&1 || { echo "lake not found. Install elan (https://github.com/leanprover/elan)." >&2; exit 2; }
OUT=$(mktemp -d "${TMPDIR:-/tmp}/verify_mathlib.XXXXXX")
status=0
for f in Core LemmaJ Scaling Bridge Interval ExamplesLemmaJ ExamplesScaling; do
  if grep -nE '\bsorry\b|\badmit\b|native_decide|^[[:space:]]*((private|protected|noncomputable)[[:space:]]+)*(axiom|opaque)[[:space:]]|skipKernelTC|debug\.|\bunsafe\b|implemented_by|@\[extern' "QAuditAnalytic/$f.lean"; then
    echo "FAIL  $f.lean: forbidden construct"; status=1
  fi
done
[ "$status" -eq 0 ] || { echo "SOME MATHLIB CHECKS FAILED"; exit 1; }
lake exe cache get > "$OUT/cache.txt" 2>&1 || { echo "FAIL  lake exe cache get (see $OUT/cache.txt)"; exit 1; }
lake build > "$OUT/build.txt" 2>&1 || { echo "FAIL  lake build (see $OUT/build.txt)"; exit 1; }
for f in Core LemmaJ Scaling Bridge Interval ExamplesLemmaJ ExamplesScaling; do
  out=$(lake env lean "QAuditAnalytic/$f.lean" 2>&1); rc=$?
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
echo "outputs: $OUT"
if [ "$status" -eq 0 ]; then echo "ALL MATHLIB CHECKS PASSED"; else echo "SOME MATHLIB CHECKS FAILED"; fi
exit $status
