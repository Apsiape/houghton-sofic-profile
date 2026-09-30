"""The doubling endomorphism psi and the cheap letters t, rho.

psi(a) = a^2, psi(b) = b^2, psi(x) = [a^2, b^2] = a^2 b^2 a^-2 b^-2.
Pi = s_1 s_2 s_0 s_1.
R' = t rho t^-1 . rho . t rho t^-1          (N4: rho^b = R')
R  = t^-1 . R' . R'(t rho, R') . t . rho . R'
"""
if not __debug__:
    raise SystemExit("This check uses assert statements; run it without python -O.")
from vk import (REL, Deriv, Lemma, S, Si, t_, ti_, rho_, rhoi_, comm, conjw, inv, red, psi,
                W_ALPHA, check_cert)
from lemmas_small import L, build_small

WA = W_ALPHA
WAi = inv(W_ALPHA)
PI = [S(1), S(2), S(0), S(1)]
PIi = [Si(1), Si(0), Si(2), Si(1)]


def shift(toks, k):
    """a^k (tokens) a^-k for sigma tokens."""
    out = []
    for w in toks:
        out.append(red('a' * k + w + 'A' * k))
    return out


def rp_tokens(u, v):
    """R'(u, v) = u v u^-1 v u v u^-1 as tokens (u, v words)."""
    return [u, v, inv(u), v, u, v, inv(u)]


RP = rp_tokens(t_, rho_)
RPw = red(''.join(RP))
RHOB = conjw(rho_, 'b')          # rho^b = b^-1 rho b
RHOB2 = conjw(rho_, 'bb')


def r_tokens():
    """R = t^-1 R' R'(t rho, R') t rho R' as a flat token list over t^+-1, rho^+-1."""
    toks = [ti_] + RP
    # R'(t rho, R'): u = t rho, v = R'
    u = [t_, rho_]
    ui = [rhoi_, ti_]
    v = RP
    for part in (u, v, ui, v, u, v, ui):
        toks += part
    toks += [t_, rho_] + RP
    return toks


Rtoks = r_tokens()
Rw = red(''.join(Rtoks))


def lemma_N4():
    """rho^b = R' with 14 cells (filling A)."""
    d = Deriv('N4', ['B', rho_, 'b', t_, rhoi_, ti_, rhoi_, t_, rhoi_, ti_])
    aba = 'ABxba'                    # x^{ba}
    abai = inv(aba)
    d.apply_run(1, 2, [aba], REL['r4'], 'rho -> x^{ba}')
    for idx in (4, 6, 8):
        d.apply_run(idx, idx + 1, [abai], REL['r4'], 'rho^-1 -> x^{-ba}')
    # now: x^{bab} x^{-b^2} x^{-ba} x^{-b^2}; conjugate by (bab)^-1 through a rotation
    d.free(['BAB', 'x', 'bab', 'BB', 'X', 'bb', 'AB', 'X', 'ba', 'BB', 'X', 'bb'])
    d.rotate(1)
    # tokens: x, bab, BB, X, bb, AB, X, ba, BB, X, bb, BAB
    # = x . x^{-g} . x^{-g'} . x^{-g} with g = b a^-1 b^-1, g' = b a b^-1 a^-1 b^-1
    d.free(['x', 'baB', 'X', 'bAB', 'b', 'a', 'bAB', 'X', 'baB', 'A', 'B', 'baB', 'X', 'bAB'])
    # R-b: b a b^-1 = x^-1 a ; b a^-1 b^-1 = a^-1 x
    for _ in range(3):
        i = d.cur.index('baB')
        d.apply_run(i, i + 1, ['X', 'a'], REL['r4'], 'R-b')
    for _ in range(3):
        i = d.cur.index('bAB')
        d.apply_run(i, i + 1, ['A', 'x'], REL['r4'], 'R-b inverse')
    # word is now x^-1 ... ; reduce to s_1^-1 x (b x^-1 b^-1) x^-1 s_1^-1 x
    d.free([Si(1), 'x', 'bXB', 'X', Si(1), 'x'])
    d.apply_run(2, 3, [Si(1)], REL['r5'], 'b x^-1 b^-1 -> s_1^-1')
    d.apply_run(1, 2, ['X'], REL['r1'], 'x -> x^-1')
    d.apply_run(5, 6, ['X'], REL['r1'], 'x -> x^-1')
    d.apply_run(0, 6, [], REL['r2'], '(s_1^-1 x^-1)^3')
    return d.done('rho^b = t rho t^-1 rho t rho t^-1')


def lemma_ARHO():
    """[x, rho] with 5 cells."""
    d = Deriv('[x,rho]', ['x', 'ABa', 'bXB', 'Aba'])
    d.apply_run(2, 3, [Si(1)], REL['r5'])
    d.free(['x', 'A', 'B', Si(2), 'b', 'a'])
    d.apply_run(2, 5, [Si(1)], L['E(1)'], 'b^-1 s_2^-1 b -> s_1^-1')
    d.free([])
    return d.done()


def lemma_CONV():
    """psi(x) = [a^2,b^2] = Pi with 6 cells."""
    c = 'abAB'
    d = Deriv('CONV', ['a', c, 'A', 'a', 'b', c, 'B', 'A', c, 'b', c, 'B'] + PIi)
    for _ in range(4):
        i = d.cur.index(c)
        d.apply_run(i, i + 1, ['x'], REL['r4'], '[a,b] -> x')
    # a x A a b x B A x b x B Pi^-1
    d.free(['a', 'x', 'A', 'a', 'b', 'x', 'B', 'A', 'x', 'b', 'x', 'B'] + PIi)
    d.apply_run(9, 12, [S(1)], REL['r5'], 'b x b^-1 -> s_1')
    d.apply_run(4, 7, [S(1)], REL['r5'], 'b x b^-1 -> s_1')
    d.free([])
    return d.done('[a^2,b^2] = s_1 s_2 s_0 s_1')


def lemma_BRAID():
    """s_1 s_0 s_1 = s_0 s_1 s_0 with 4 cells."""
    d = Deriv('BRAID', [S(1), S(0), S(1), Si(0), Si(1), Si(0)])
    d.apply_run(3, 4, [S(0)], REL['r1'])
    d.apply_run(4, 5, [S(1)], REL['r1'])
    d.apply_run(5, 6, [S(0)], REL['r1'])
    d.apply_run(0, 6, [], REL['r2'])
    return d.done()


def conv_all(d, conv, pos_word_pairs):
    for w, repl in pos_word_pairs:
        i = d.cur.index(w)
        d.apply_run(i, i + 1, repl, conv, 'psi(x) -> Pi')


def lemma_psi_r1(conv):
    d = Deriv('psi(r1)', [WA, WA])
    conv_all(d, conv, [(WA, PI), (WA, PI)])
    # s1 s2 s0 s1 s1 s2 s0 s1
    d.apply_run(3, 5, [], REL['r1'], 's1 s1')
    # s1 s2 s0 s2 s0 s1
    d.apply_run(2, 4, [S(2), S(0)], REL['r3'], 's0 s2 -> s2 s0')
    d.apply_run(1, 3, [], REL['r1'])
    d.apply_run(1, 3, [], REL['r1'])
    d.apply_run(0, 2, [], REL['r1'])
    return d.done()


def lemma_psi_r5(conv):
    d = Deriv('psi(r5)', ['aa', WA, 'AA', 'bb', WAi, 'BB'])
    conv_all(d, conv, [(WA, PI), (WAi, PIi)])
    toks = shift(PI, 2)
    for i in (1, 0, 2, 1):
        toks += ['b', 'b', Si(i), 'B', 'B']
    d.free(toks)
    for blk in range(4):
        # the block after the 4 shifted letters
        base = 4 + blk
        i = [1, 0, 2, 1][blk]
        assert d.cur[base:base + 5] == ['b', 'b', Si(i), 'B', 'B'], d.cur[base:base + 5]
        d.apply_run(base + 1, base + 4, [Si(i + 1)], L['E(%d)' % i], 'b s_i^-1 b^-1 -> s_{i+1}^-1')
        d.apply_run(base, base + 3, [Si(i + 2)], L['E(%d)' % (i + 1)])
    d.free([])
    return d.done()


def A_lemma(w):
    return L['A(%d)' % w] if w >= 3 else REL['r3']


def lemma_psi_r3(conv):
    d = Deriv('psi(r3)', [WA, 'aaaa', WA, 'AAAA', WAi, 'aaaa', WAi, 'AAAA'])
    conv_all(d, conv, [(WA, PI), (WA, PI), (WAi, PIi), (WAi, PIi)])
    P = PI
    Q = shift(PI, 4)
    d.free(P + Q + [inv(w) for w in reversed(P)] + [inv(w) for w in reversed(Q)])
    # move each letter of Q (last first) right past the four letters of P^-1
    for qpos in range(7, 3, -1):
        for step in range(4):
            i = qpos + step
            lq = d.cur[i]
            pi_ = d.cur[i + 1]
            # widths: lq = s_l, pi_ = s_k^-1
            l = int(len(lq) // 2)
            k = int(len(pi_) // 2)
            d.apply_run(i, i + 2, [pi_, lq], A_lemma(abs(l - k)), 'swap width %d' % abs(l - k))
    d.free([])
    return d.done()


def sig_index(tok):
    return len(tok) // 2          # S(j) = a^j x A^j for j >= 0


def coxeter_reduce(d, M):
    """Lemma C's coset procedure on a positive word in S(0..M-1) (the whole token list)."""
    sw = {w: A_lemma(w) for w in range(2, 7)}
    braid = L['BRAID']
    while M >= 1:
        letters = [sig_index(t) for t in d.cur]
        assert all(0 <= g < M for g in letters), (letters, M)
        # h = d.cur[:lh], block = c_k = [M-1, ..., k] at d.cur[lh:lh+M-k], next input at p
        lh = 0
        k = M
        p = 0
        n_in = len(d.cur)
        consumed = 0
        while consumed < n_in:
            p = lh + (M - k)
            g = sig_index(d.cur[p])
            consumed += 1
            if g <= k - 2:
                for q in range(p, lh, -1):
                    a_, b_ = d.cur[q - 1], d.cur[q]
                    d.apply_run(q - 1, q + 1, [b_, a_], sw[abs(sig_index(a_) - g)], 'M2')
                lh += 1
            elif g == k - 1:
                k -= 1
            elif g == k:
                d.apply_run(p - 1, p + 1, [], REL['r1'], 'M1')
                k += 1
            else:
                # block: M-1 ... i+1, i, i-1, ..., k ; append g = i at p
                i = g
                # move g left past k, ..., i-2
                q = p
                while sig_index(d.cur[q - 1]) <= i - 2:
                    a_, b_ = d.cur[q - 1], d.cur[q]
                    d.apply_run(q - 1, q + 1, [b_, a_], sw[abs(sig_index(a_) - i)], 'M2')
                    q -= 1
                # now d.cur[q-2:q+1] = s_i s_{i-1} s_i
                assert [sig_index(t) for t in d.cur[q - 2:q + 1]] == [i, i - 1, i], d.cur[q - 2:q + 1]
                d.apply_run(q - 2, q + 1, [S(i - 1), S(i), S(i - 1)], braid, 'M3')
                q = q - 2           # front s_{i-1}
                while q > lh:
                    a_, b_ = d.cur[q - 1], d.cur[q]
                    d.apply_run(q - 1, q + 1, [b_, a_], sw[abs(sig_index(a_) - (i - 1))], 'M2')
                    q -= 1
                lh += 1
        assert k == M, (k, M)
        assert len(d.cur) == lh
        M -= 1
    assert d.cur == [], d.cur


def lemma_psi_r2(conv):
    d = Deriv('psi(r2)', [WA, 'aa', WA, 'AA'] * 3)
    conv_all(d, conv, [(WA, PI)] * 6)
    d.free((PI + shift(PI, 2)) * 3)
    coxeter_reduce(d, 5)
    return d.done()


def lemma_PSIRHO(N4):
    """psi(rho) = R with 6 uses of N4 (84 cells)."""
    toks = [ti_, RHOB, RHOB2, t_, rho_, RHOB]
    assert red(''.join(toks)) == red(psi(rho_)), 'free identity (e3) fails'
    Ri = [inv(w) for w in reversed(Rtoks)]
    d = Deriv('psi(rho)=R', toks + Ri)
    d.apply_run(1, 2, RP, N4, 'rho^b -> R\'')
    i = d.cur.index(RHOB)       # the last rho^b of psi(rho)
    d.apply_run(i, i + 1, RP, N4, 'rho^b -> R\'')
    i = d.cur.index(RHOB2)
    # rho^{b^2} = b^-1 rho^b b -> b^-1 R' b  (one N4), then = R'(t^b, rho^b) freely, t^b = t rho freely
    d.free(d.cur[:i] + ['B', RHOB, 'b'] + d.cur[i + 1:])
    d.apply_run(i + 1, i + 2, RP, N4, 'rho^b -> R\' inside b-conjugate')
    tb = conjw(t_, 'b')
    assert tb == red(t_ + rho_), 'free identity (e2) fails'
    # b^-1 R' b = R'(t^b, rho^b) freely; write it with t^b = t rho
    mid = []
    for w in RP:
        if w == t_:
            mid += [t_, rho_]
        elif w == ti_:
            mid += [rhoi_, ti_]
        else:
            mid += [RHOB]
    d.free(d.cur[:i] + mid + d.cur[i + 1 + len(RP) + 1:])
    for _ in range(3):
        j = d.cur.index(RHOB)
        d.apply_run(j, j + 1, RP, N4, 'rho^b -> R\'')
    d.free([])
    return d.done('psi(rho) = R')


def build_psi():
    if 'A(2)' not in L:
        build_small()
    L['N4'] = lemma_N4()
    L['[x,rho]'] = lemma_ARHO()
    L['CONV'] = lemma_CONV()
    L['BRAID'] = lemma_BRAID()
    conv = L['CONV']
    L['psi(r1)'] = lemma_psi_r1(conv)
    L['psi(r5)'] = lemma_psi_r5(conv)
    L['psi(r3)'] = lemma_psi_r3(conv)
    L['psi(r2)'] = lemma_psi_r2(conv)
    L['psi(r4)'] = Lemma('psi(r4)', psi(REL['r4'].word), [], 'freely trivial')
    assert L['psi(r4)'].word == '' and check_cert(psi(REL['r4'].word), [])
    for i in (1, 2, 3, 5):
        assert L['psi(r%d)' % i].word == red(psi(REL['r%d' % i].word))
    L['psi(rho)=R'] = lemma_PSIRHO(L['N4'])
    return L


if __name__ == '__main__':
    build_psi()
    claimed = {'N4': 14, '[x,rho]': 5, 'CONV': 6, 'BRAID': 4, 'psi(r1)': 17, 'psi(r5)': 182,
               'psi(r3)': 864, 'psi(r2)': 359, 'psi(r4)': 0, 'psi(rho)=R': 84}
    for k, v in claimed.items():
        c = L[k].cost
        print('%-11s cells %5d   claimed <= %5d   %s' % (k, c, v, 'OK' if c <= v else 'EXCEEDS'))
    print('free identities: psi(t) = t rho t:', red(psi(t_)) == red(t_ + rho_ + t_),
          '| t^b = t rho:', conjw(t_, 'b') == red(t_ + rho_),
          '| psi(rho) = t^-1 rho^b rho^{b^2} t rho rho^b:',
          red(psi(rho_)) == red(ti_ + RHOB + RHOB2 + t_ + rho_ + RHOB))
    print('|R\'| =', len(RP), ' |R| =', len(Rtoks), ' #rho(R) =', sum(1 for w in Rtoks if w in (rho_, rhoi_)))
