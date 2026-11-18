#!/usr/bin/env bash
# Rerun every script of this archive and compare with expected/.
# Usage: ./verify_python.sh            (uses python3; set PYTHON=/path/to/python to change)
# Requirements: see requirements.txt (SymPy 1.14 for the exact scripts).
# Script outputs are written to a temporary directory, not to the archive.
set -u
cd "$(dirname "$0")"
PY="${PYTHON:-python3}"
"$PY" -I -c "import sys, numpy, scipy, sympy, mpmath; print('Python', sys.version.split()[0], 'NumPy', numpy.__version__, 'SciPy', scipy.__version__, 'SymPy', sympy.__version__, 'mpmath', mpmath.__version__)" || { echo "missing Python packages: pip install -r python/requirements.txt (from the root of the archive)"; exit 2; }
status=0
OUT=$(mktemp -d "${TMPDIR:-/tmp}/verify_python.XXXXXX")
run() {  # $1 = directory, $2 = script, $3 = mode (exact | numeric)
  local d="$1" s="$2" mode="$3" base="${2%.py}"
  local out="$OUT/out_$base.txt" exp="expected/salida_$base.txt"
  "$PY" -I "$d/$s" > "$out" 2>&1; local rc=$?
  if [ "$rc" -ne 0 ]; then echo "FAIL  $d/$s: exit code $rc (see $out)"; status=1; return; fi
  if "$PY" -I compare_outputs.py "$out" "$exp" "$mode"; then
    echo "OK    $d/$s ($mode): $(tail -1 "$out")"
  else
    echo "FAIL  $d/$s: output differs from $exp"; status=1
  fi
}
for s in v12_familia_escala.py v3_modelos_apuntados.py v4_historias_ac.py v5_rkp_cadenas.py gauss_conexiones.py; do
  run exact "$s" exact
done
run exact escalado_diagonal_escalar.py numeric
run high_precision contraejemplo_diagonal_fija.py numeric
for s in J_conectividad.py pistas_numerico.py banda_monotonia.py monotonia_escalado.py; do
  run numeric "$s" numeric
done
echo "script outputs: $OUT"
if [ "$status" -eq 0 ]; then echo "ALL PYTHON CHECKS PASSED"; else echo "SOME PYTHON CHECKS FAILED"; fi
exit $status
