"""Small lemmas: the transfer and halving lemmas at the parameters the area chain uses.

Definitions (areas in Johnson's presentation P):
  A(d) = Area [s_0, s_d]           s_j = a^j x a^-j
  E(i) = Area [s_i, t]             t = b^-1 a
  U(j) = Area (tau_j s_j^-1)       tau_j = b^j x b^-j
  B(k) = Area [s_-k, b]            (k >= 2)
  B0   = Area [x, s_1 s_0 b]
"""
from vk import (REL, Deriv, S, Si, TAU, Tk, t_, ti_, comm, apow, bpow, inv, red)

L = {}


def lemma_A2():
    d = Deriv('A(2)', [S(0), S(2), Si(0), Si(2)])
    d.step([], REL['r3'])
    return d.done('r3 itself')


def lemma_E0():
    d = Deriv('E(0)', [S(0), t_, Si(0), ti_])
    d.step([], REL['r5'])
    return d.done('[x,t] is a rotation of r5^-1')


def lemma_E(i):
    """E(i) <= 2i + 1 + sum_{d=2}^{i+1} A(d)   (i >= 1)."""
    d = Deriv('E(%d)' % i, [S(i), t_, Si(i), ti_])
    # t = t_1 s_-1 = t_2 s_0 s_-1 = ... = t_i s_{i-2} ... s_-1   (one r4 cell each)
    for k in range(i):
        pos = 1
        cur = d.cur
        # token Tk(k) sits at position 1
        assert cur[pos] == Tk(k), (cur, k)
        d.apply_run(pos, pos + 1, [Tk(k + 1), S(k - 1)], REL['r4'], 't_%d -> t_%d s_%d' % (k, k + 1, k - 1))
    # t^-1 = s_-1^-1 ... s_{i-2}^-1 t_i^-1
    for k in range(i):
        pos = len(d.cur) - 1
        assert d.cur[pos] == inv(Tk(k)), (d.cur, k)
        d.apply_run(pos, pos + 1, [Si(k - 1), inv(Tk(k + 1))], REL['r4'], 't_%d^-1' % k)
    # tokens: S(i), T_i, S(i-2..-1), Si(i), Si(-1..i-2), T_i^-1
    # move Si(i) left past S(-1), S(0), ..., S(i-2)
    for l in range(-1, i - 1):
        idx = d.cur.index(Si(i))
        assert d.cur[idx - 1] == S(l), (d.cur, l)
        d.apply_run(idx - 1, idx + 1, [Si(i), S(l)], L['A(%d)' % (i - l)], 'swap s_%d, s_%d^-1' % (l, i))
    d.free([S(i), Tk(i), Si(i), inv(Tk(i))])
    d.step([], REL['r5'], '[s_i, t_i] = a^i [x,t] a^-i')
    return d.done()


def lemma_U(j):
    """U(j) <= U(j-1) + E(j-1)."""
    d = Deriv('U(%d)' % j, [TAU(j), Si(j)])
    d.free(['b', TAU(j - 1), 'B', Si(j)])
    if j - 1 >= 1:
        d.step(['b', S(j - 1), 'B', Si(j)], L['U(%d)' % (j - 1)], 'tau_%d -> s_%d' % (j - 1, j - 1))
    d.step([], L['E(%d)' % (j - 1)], 'b s_i b^-1 s_{i+1}^-1 = b[s_i,t]b^-1')
    return d.done()


def lemma_B0():
    d = Deriv('B0', ['x', S(1), S(0), 'b', 'X', 'B', Si(0), Si(1)])
    d.step(['x', S(1), S(0), Si(1), Si(0), Si(1)], REL['r5'], 'b x^-1 b^-1 -> s_1^-1')
    d.step(['x', S(1), S(0), S(1), Si(0), Si(1)], REL['r1'])
    d.step(['x', S(1), S(0), S(1), S(0), Si(1)], REL['r1'])
    d.step(['x', S(1), S(0), S(1), S(0), S(1)], REL['r1'])
    d.step([], REL['r2'], '(s_0 s_1)^3')
    return d.done()


def Y(m):
    return red(apow(m) + 'b' + apow(-m))


def lemma_B(k):
    """B(k) <= 2k + 5 + sum_{d=2}^{k-1} A(d)."""
    d = Deriv('B(%d)' % k, [S(-k), 'b', Si(-k), 'B'])
    d.free([apow(-k), 'x', Y(k), 'X', inv(Y(k)), apow(k)])
    # a^m b a^-m = s_{m-1} (a^{m-1} b a^{-(m-1)}): one r4 cell each
    for m in range(k, 0, -1):
        idx = d.cur.index(Y(m))
        d.apply_run(idx, idx + 1, [S(m - 1), Y(m - 1)], REL['r4'], 'Y_%d' % m)
    for m in range(k, 0, -1):
        idx = d.cur.index(inv(Y(m)))
        d.apply_run(idx, idx + 1, [inv(Y(m - 1)), Si(m - 1)], REL['r4'], 'Y_%d^-1' % m)
    # tokens: A^k, x, S(k-1..0), b, X, B, Si(0..k-1), a^k
    for l in range(k - 1, 1, -1):
        idx = d.cur.index('x')
        assert d.cur[idx + 1] == S(l)
        d.apply_run(idx, idx + 2, [S(l), 'x'], L['A(%d)' % l], 'swap x, s_%d' % l)
    idx = d.cur.index('x')
    run = ['x', S(1), S(0), 'b', 'X', 'B', Si(0), Si(1)]
    assert d.cur[idx:idx + 8] == run, d.cur
    d.apply_run(idx, idx + 8, [], L['B0'], 'B0')
    d.free([])
    return d.done()


def lemma_halving(k, j):
    """A(k+j) <= A(k) + 2j B(k) + 2U(j)."""
    m = k + j
    d = Deriv('A(%d)' % m, [S(0), S(m), Si(0), Si(m)])
    d.free([apow(k), S(-k), S(j), Si(-k), Si(j), apow(-k)])
    if j >= 1:
        d.apply_run(2, 3, [TAU(j)], L['U(%d)' % j], 's_j -> tau_j')
        d.apply_run(4, 5, [inv(TAU(j))], L['U(%d)' % j], 's_j^-1 -> tau_j^-1')
    toks = [apow(k), S(-k)] + ['b'] * j + ['x'] + ['B'] * j + [Si(-k)] + ['b'] * j + ['X'] + ['B'] * j + [apow(-k)]
    d.free(toks)
    Bk = L['B(%d)' % k]
    for _ in range(j):
        idx = d.cur.index(S(-k))
        assert d.cur[idx + 1] == 'b'
        d.apply_run(idx, idx + 2, ['b', S(-k)], Bk, 's_-k past b')
    for _ in range(j):
        idx = d.cur.index(Si(-k))
        assert d.cur[idx - 1] == 'B'
        d.apply_run(idx - 1, idx + 1, [Si(-k), 'B'], Bk, 's_-k^-1 past b^-1')
    d.free([apow(k)] + ['b'] * j + [S(-k), 'x', Si(-k), 'X'] + ['B'] * j + [apow(-k)])
    d.apply_run(1 + j, 5 + j, [], L['A(%d)' % k], '[s_-k, x] = a^-k [s_0, s_k] a^k')
    d.free([])
    return d.done('halving lemma, k=%d, j=%d' % (k, j))


def build_small():
    L['A(2)'] = lemma_A2()
    L['E(0)'] = lemma_E0()
    L['U(1)'] = lemma_U(1)
    L['E(1)'] = lemma_E(1)
    L['U(2)'] = lemma_U(2)
    L['B0'] = lemma_B0()
    L['B(2)'] = lemma_B(2)
    L['A(3)'] = lemma_halving(2, 1)
    L['A(4)'] = lemma_halving(2, 2)
    L['E(2)'] = lemma_E(2)
    L['U(3)'] = lemma_U(3)
    L['B(3)'] = lemma_B(3)
    L['A(5)'] = lemma_halving(3, 2)
    L['A(6)'] = lemma_halving(3, 3)
    L['E(3)'] = lemma_E(3)
    return L


if __name__ == '__main__':
    build_small()
    claimed = {'A(2)': 1, 'E(0)': 1, 'U(1)': 1, 'E(1)': 4, 'U(2)': 5, 'B0': 5, 'B(2)': 9, 'A(3)': 21,
               'A(4)': 47, 'E(2)': 27, 'U(3)': 32, 'B(3)': 12, 'A(5)': 79, 'A(6)': 157, 'E(3)': 76}
    for k, v in L.items():
        print('%-6s cells %5d   claimed <= %5d   %s' % (k, v.cost, claimed[k], 'OK' if v.cost <= claimed[k] else 'EXCEEDS'))
