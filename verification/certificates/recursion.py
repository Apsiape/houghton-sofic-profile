"""The doubling recursion, executed: certificates for X_n = W_n, U(n) = Area[x, X_n], and
A(m) = Area[s_0, s_m] via the halving lemma at k = 2, for small n and m.

X_n = b^-n a^n.  W_1 = t,  W_2n = W_n(t rho t, R),  W_2n+1 = W_2n(t rho, R') t.
Rw(n) = cells in the certificate of X_n W_n^-1.
"""
if not __debug__:
    raise SystemExit("This check uses assert statements; run it without python -O.")
import sys
import time
from vk import (REL, Deriv, Lemma, S, Si, t_, ti_, rho_, rhoi_, comm, inv, red, psi, psi_cells,
                check_cert, apow, bpow)
from lemmas_small import L
from lemmas_psi import build_psi, Rtoks, RP, RPw, RHOB

TOK_INV = {t_: ti_, ti_: t_, rho_: rhoi_, rhoi_: rho_}


def inv_toks(toks):
    return [TOK_INV[w] for w in reversed(toks)]


IMG_D = {t_: [t_, rho_, t_], rho_: list(Rtoks)}
IMG_D[ti_] = inv_toks(IMG_D[t_])
IMG_D[rhoi_] = inv_toks(IMG_D[rho_])
IMG_B = {t_: [t_, rho_], rho_: list(RP)}
IMG_B[ti_] = inv_toks(IMG_B[t_])
IMG_B[rhoi_] = inv_toks(IMG_B[rho_])


def X(n):
    return bpow(-n) + apow(n)


def count_rho(toks):
    return sum(1 for w in toks if w in (rho_, rhoi_))


def build(N):
    build_psi()
    psi_rel = {'r%d' % i: L['psi(r%d)' % i] for i in range(1, 6)}
    W = {1: [t_]}
    cert = {1: Lemma('X_1=W_1', X(1) + inv(t_), [])}
    assert red(X(1) + inv(t_)) == ''
    bound = {1: 0}
    for n in range(2, N + 1):
        if n % 2 == 0:
            m = n // 2
            Wm = W[m]
            W[n] = [w for s in Wm for w in IMG_D[s]]
            toks = [X(n)] + [red(''.join(inv_toks(IMG_D[s]))) for s in reversed(Wm)]
            d = Deriv('X_%d=W_%d' % (n, n), toks)
            Rword = red(''.join(Rtoks))
            for idx, s in enumerate(reversed(Wm)):
                pos = 1 + idx
                if s == rho_:
                    d.apply_run(pos, pos + 1, [inv(psi(rho_))], L['psi(rho)=R'], 'R^-1 -> psi(rho)^-1')
                elif s == rhoi_:
                    d.apply_run(pos, pos + 1, [psi(rho_)], L['psi(rho)=R'], 'R -> psi(rho)')
            J = red(psi(X(m) + inv(red(''.join(Wm)))))
            cells = psi_cells(cert[m].cells, psi_rel)
            lem = Lemma('psi(X_%d W_%d^-1)' % (m, m), J, cells)
            d.apply_run(0, len(d.cur), [], lem, 'psi-transport')
            cert[n] = d.done()
            bound[n] = 864 * bound[m] + 84 * count_rho(Wm)
        else:
            m = n - 1
            Wm = W[m]
            W[n] = [w for s in Wm for w in IMG_B[s]] + [t_]
            toks = [X(n), ti_] + [red(''.join(inv_toks(IMG_B[s]))) for s in reversed(Wm)]
            d = Deriv('X_%d=W_%d' % (n, n), toks)
            for idx, s in enumerate(reversed(Wm)):
                pos = 2 + idx
                if s == rho_:
                    d.apply_run(pos, pos + 1, [inv(RHOB)], L['N4'], "R'^-1 -> rho^-b")
                elif s == rhoi_:
                    d.apply_run(pos, pos + 1, [RHOB], L['N4'], "R' -> rho^b")
            J = red('B' + X(m) + inv(red(''.join(Wm))) + 'b')
            cells = [(red('B' + z), r, s) for (z, r, s) in cert[m].cells]
            lem = Lemma('b-conjugate of X_%d W_%d^-1' % (m, m), J, cells)
            d.apply_run(0, len(d.cur), [], lem, 'conjugation by b')
            cert[n] = d.done()
            bound[n] = bound[m] + 14 * count_rho(Wm)
    return W, cert, bound


def lemma_Ux(n, W, cert):
    """[x, X_n] <= 2 Rw(n) + #t + 5 #rho."""
    Wn = W[n]
    d = Deriv('[x,X_%d]' % n, ['x', X(n), 'X', inv(X(n))])
    d.apply_run(1, 2, list(Wn), cert[n], 'X_n -> W_n')
    j = d.cur.index(inv(X(n)))
    d.apply_run(j, j + 1, inv_toks(Wn), cert[n], 'X_n^-1 -> W_n^-1')
    for _ in range(len(Wn)):
        i = d.cur.index('x')
        l_ = d.cur[i + 1]
        lem = REL['r5'] if l_ in (t_, ti_) else L['[x,rho]']
        d.apply_run(i, i + 2, [l_, 'x'], lem, 'x past letter')
    d.free([])
    return d.done()


def lemma_A_via_U(m, Ulem):
    """A(m) <= A(2) + 2(m-2) B(2) + 2 U(m-2)   (halving lemma at k = 2)."""
    k, j = 2, m - 2
    d = Deriv('A(%d)' % m, [S(0), S(m), Si(0), Si(m)])
    d.free([apow(k), S(-k), S(j), Si(-k), Si(j), apow(-k)])
    TAUj = red(bpow(j) + 'x' + bpow(-j))
    d.apply_run(2, 3, [TAUj], Ulem, 's_j -> tau_j')
    d.apply_run(4, 5, [inv(TAUj)], Ulem, 's_j^-1 -> tau_j^-1')
    d.free([apow(k), S(-k)] + ['b'] * j + ['x'] + ['B'] * j + [Si(-k)] + ['b'] * j + ['X'] + ['B'] * j + [apow(-k)])
    for _ in range(j):
        i = d.cur.index(S(-k))
        d.apply_run(i, i + 2, ['b', S(-k)], L['B(2)'])
    for _ in range(j):
        i = d.cur.index(Si(-k))
        d.apply_run(i - 1, i + 1, [Si(-k), 'B'], L['B(2)'])
    d.free([apow(k)] + ['b'] * j + [S(-k), 'x', Si(-k), 'X'] + ['B'] * j + [apow(-k)])
    d.apply_run(1 + j, 5 + j, [], L['A(2)'])
    d.free([])
    return d.done()


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    t0 = time.time()
    W, cert, bound = build(N)
    print('n  |W_n|  #rho   Rw(n) cells   recursion bound   U(n) cells   2Rw+#t+5#rho')
    U = {}
    for n in range(1, N + 1):
        U[n] = lemma_Ux(n, W, cert)
        r = count_rho(W[n])
        print('%-2d %6d %5d %12d %17d %12d %14d' % (n, len(W[n]), r, cert[n].cost, bound[n], U[n].cost,
                                                     2 * cert[n].cost + (len(W[n]) - r) + 5 * r))
    print()
    direct = {3: 21, 4: 47, 5: 79, 6: 157}
    print('m   A(m) cells via U(m-2)   direct small-lemma value   m^11')
    for m in range(3, N + 3):
        a = lemma_A_via_U(m, U[m - 2])
        print('%-3d %20d %24s %10d' % (m, a.cost, direct.get(m, '-'), m ** 11))
    print('time %.1fs' % (time.time() - t0))
