"""Build every certificate of the area chain and export the flattened ones.

Usage:  python build_all.py [N_EXPORT]     (default 5; recursion instances n <= N_EXPORT are exported)
Output: out/certificates.json.gz  and a summary table on stdout.
"""
if not __debug__:
    raise SystemExit("This check uses assert statements; run it without python -O.")
import gzip
import json
import os
import sys
import time

from lemmas_small import L, build_small
from lemmas_psi import build_psi
from recursion import build, lemma_Ux, lemma_A_via_U

CLAIMED = {'A(2)': 1, 'E(0)': 1, 'U(1)': 1, 'E(1)': 4, 'U(2)': 5, 'B0': 5, 'B(2)': 9, 'A(3)': 21,
           'A(4)': 47, 'E(2)': 27, 'U(3)': 32, 'B(3)': 12, 'A(5)': 79, 'A(6)': 157, 'E(3)': 76,
           'N4': 14, '[x,rho]': 5, 'CONV': 6, 'BRAID': 4, 'psi(r1)': 17, 'psi(r5)': 182,
           'psi(r3)': 864, 'psi(r2)': 359, 'psi(r4)': 0, 'psi(rho)=R': 84}


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t0 = time.time()
    build_small()
    build_psi()
    W, cert, bound = build(N)
    out = []
    print('%-12s %8s %8s' % ('relation', 'cells', 'claimed'))
    for k, c in CLAIMED.items():
        lem = L[k]
        assert lem.cost <= c, (k, lem.cost, c)
        print('%-12s %8d %8d' % (k, lem.cost, c))
        out.append({'name': k, 'cells': lem.cells})
    for n in range(1, N + 1):
        out.append({'name': 'X_%d=W_%d' % (n, n), 'cells': cert[n].cells})
        u = lemma_Ux(n, W, cert)
        out.append({'name': '[x,X_%d]' % n, 'cells': u.cells})
        print('%-12s %8d %8s   (X_%d = W_%d: %d cells; recursion bound %d)' % (
            '[x,X_%d]' % n, u.cost, '-', n, n, cert[n].cost, bound[n]))
        m = n + 2
        a = lemma_A_via_U(m, u)
        out.append({'name': 'A(%d)' % m if m > 6 else 'A(%d)/via-U' % m, 'cells': a.cells})
        print('%-12s %8d %8s   (via [x,X_%d]; m^11 = %d)' % ('A(%d)' % m, a.cost, '-', n, m ** 11))
    os.makedirs('out', exist_ok=True)
    with gzip.open('out/certificates.json.gz', 'wt', encoding='ascii') as f:
        json.dump({'format': 'cells (z, relator, sign): target == prod z r^sign z^-1 in the free group on a,b,x',
                   'certificates': [{'name': e['name'], 'cells': [[z, r, s] for (z, r, s) in e['cells']]}
                                    for e in out]}, f)
    print('exported %d certificates to out/certificates.json.gz (%.0f kB) in %.1fs' % (
        len(out), os.path.getsize('out/certificates.json.gz') / 1024, time.time() - t0))


if __name__ == '__main__':
    main()
