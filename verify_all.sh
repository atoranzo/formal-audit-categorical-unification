#!/usr/bin/env bash
# Run every check of this archive, in this order:
#   1. integrity: the SHA-256 sums of all its files, listed in SHA256SUMS;
#   2. the six Lean 4 files checked without Mathlib (lean/verify_lean.sh);
#   3. the eleven Python scripts (python/verify_python.sh);
#   4. the Lean 4 project with Mathlib (lean-mathlib/verify_mathlib.sh). Its first run clones
#      Mathlib and downloads its prebuilt cache (about 1 GB in all) and needs about 7 GB of disk;
#      skip it with SKIP_MATHLIB=1.
# If a file differs from SHA256SUMS, the script stops there: the archive is then not the
# one that was published. To run the checks on a modified copy anyway, set SKIP_CHECKSUMS=1.
# A summary is printed at the end. Exit code: 0 if every step that ran passed; 1 if a step
# failed; 2 if no step failed but a step could not run because a tool is missing.
# Usage:  bash verify_all.sh                    or  make verify
#         SKIP_MATHLIB=1 bash verify_all.sh     or  make verify SKIP_MATHLIB=1
# The variables of the individual scripts (LEAN, PYTHON) are passed through to them.
set -u
cd "$(dirname "$0")"

SUMMARY=""
FAILED=0
NOTRUN=0
SKIPPED=""

record() {  # $1 = step, $2 = result
  SUMMARY="$SUMMARY$(printf '%-34s %s' "$1" "$2")
"
}

summary_and_exit() {
  echo
  echo "================================ Summary ================================"
  printf '%s' "$SUMMARY"
  echo "========================================================================="
  if [ "$FAILED" -ne 0 ]; then
    echo "SOME CHECKS FAILED"; exit 1
  elif [ "$NOTRUN" -ne 0 ]; then
    echo "SOME CHECKS COULD NOT RUN (a tool is missing; see the messages above)"; exit 2
  elif [ -n "$SKIPPED" ]; then
    echo "ALL CHECKS THAT RAN PASSED (skipped:$SKIPPED)"; exit 0
  else
    echo "ALL CHECKS PASSED"; exit 0
  fi
}

run_step() {  # $1 = step, $2 = script
  echo
  echo "==> $1: bash $2"
  local start=$SECONDS
  bash "$2"
  local rc=$?
  local took="$((SECONDS - start)) s"
  case "$rc" in
    0) record "$1" "PASSED ($took)" ;;
    2) record "$1" "NOT RUN: a tool is missing"; NOTRUN=1 ;;
    *) record "$1" "FAILED (exit code $rc)"; FAILED=1 ;;
  esac
}

# 1. Integrity
STEP="Integrity (SHA256SUMS)"
echo "==> $STEP"
if [ "${SKIP_CHECKSUMS:-0}" = "1" ]; then
  echo "skipped (SKIP_CHECKSUMS=1)"
  record "$STEP" "SKIPPED (SKIP_CHECKSUMS=1)"; SKIPPED="$SKIPPED checksums"
else
  if command -v sha256sum > /dev/null 2>&1; then
    sha256sum -c --quiet SHA256SUMS; rc=$?
  elif command -v shasum > /dev/null 2>&1; then
    shasum -a 256 -c --quiet SHA256SUMS; rc=$?
  else
    echo "neither sha256sum nor shasum was found" >&2; rc=127
  fi
  if [ "$rc" -eq 0 ]; then
    echo "OK    all $(grep -c . SHA256SUMS) files match SHA256SUMS"
    record "$STEP" "PASSED"
  elif [ "$rc" -eq 127 ]; then
    record "$STEP" "NOT RUN: no sha256sum or shasum"; NOTRUN=1
  else
    echo "FAIL  the files listed above differ from SHA256SUMS or are missing:"
    echo "      this is not the archive as it was published."
    echo "      To run the checks on a modified copy anyway, set SKIP_CHECKSUMS=1."
    record "$STEP" "FAILED"; FAILED=1
    summary_and_exit
  fi
fi

# 2-4. Lean without Mathlib, Python, Lean with Mathlib
run_step "Lean without Mathlib [L]" lean/verify_lean.sh
run_step "Python scripts [S] [N]" python/verify_python.sh
if [ "${SKIP_MATHLIB:-0}" = "1" ]; then
  echo
  echo "==> Lean with Mathlib [M]: skipped (SKIP_MATHLIB=1)"
  record "Lean with Mathlib [M]" "SKIPPED (SKIP_MATHLIB=1): [M] not checked in this run"
  SKIPPED="$SKIPPED Lean-with-Mathlib"
else
  run_step "Lean with Mathlib [M]" lean-mathlib/verify_mathlib.sh
fi

summary_and_exit
