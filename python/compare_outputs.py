"""Compare the output of a script with its expected output.
Usage: python3 -I compare_outputs.py OUTPUT EXPECTED MODE
MODE 'exact'   : the final line must be identical and no line may contain FALLO or FAIL.
MODE 'numeric' : the same, and every number must agree with the expected one within a
                 relative tolerance of 1e-3 (absolute 1e-6); local optimizers can differ
                 slightly between platforms. Number mismatches are reported as failures.
Exit code 0 if the output passes."""
import re
import sys

out_path, exp_path, mode = sys.argv[1], sys.argv[2], sys.argv[3]
out = open(out_path, encoding='utf-8').read().strip().splitlines()
exp = open(exp_path, encoding='utf-8').read().strip().splitlines()
ok = True
if not out:
    print('  empty output'); sys.exit(1)
if any(('FALLO' in l) or ('FAIL' in l) for l in out):
    print('  a check reports a failure'); ok = False
if out[-1].strip() != exp[-1].strip():
    print('  final line differs:\n    got:      %s\n    expected: %s' % (out[-1], exp[-1])); ok = False
if mode == 'numeric':
    num = re.compile(r'[-+]?\d+\.\d+(?:[eE][-+]?\d+)?')
    if len(out) != len(exp):
        print('  different number of lines (%d vs %d)' % (len(out), len(exp))); ok = False
    worst = 0.0
    for a, b in zip(out, exp):
        xa, xb = [float(x) for x in num.findall(a)], [float(x) for x in num.findall(b)]
        if len(xa) != len(xb):
            print('  line structure differs:\n    got:      %s\n    expected: %s' % (a, b)); ok = False; continue
        for u, v in zip(xa, xb):
            d = abs(u - v)
            if d > max(1e-6, 1e-3 * abs(v)):
                print('  number differs: %r vs %r in line: %s' % (u, v, b)); ok = False
            worst = max(worst, d / max(1e-12, abs(v)) if abs(v) > 1e-9 else d)
    print('  largest relative deviation: %.2e' % worst)
sys.exit(0 if ok else 1)
