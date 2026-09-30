"""Independent verifier for the area certificates (shares no code with the builder).

For every exported certificate it recomputes the target word from the definitions below,
multiplies out the cells z r^s z^-1 (r one of Johnson's five relators, s = +-1), freely reduces,
and checks that the result equals the freely reduced target.  The number of cells is then an
upper bound for the area of the target in the presentation.

Usage: python verify.py [out/certificates.json.gz]
"""
import gzip
import json
import re
import sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b', 'x': 'X', 'X': 'x'}


def red(w):
    st = []
    for c in w:
        if st and st[-1] == INV[c]:
            st.pop()
        else:
            st.append(c)
    return ''.join(st)


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def p(letter, k):                       # letter^k
    return letter * k if k >= 0 else INV[letter] * (-k)


def comm(u, v):                         # [u,v] = u v u^-1 v^-1
    return u + v + inv(u) + inv(v)


# Johnson's presentation of H_3 (Lee, arXiv:1212.0257, Theorem 2.8), a = g_1, b = g_2, x = alpha
REL = {
    'r1': 'xx',
    'r2': 'xaxA' * 3,
    'r3': comm('x', p('a', 2) + 'x' + p('a', -2)),
    'r4': 'abAB' + 'X',
    'r5': 'axA' + 'bXB',
}

sigma = lambda j: p('a', j) + 'x' + p('a', -j)       # s_j = a^j x a^-j
tau = lambda j: p('b', j) + 'x' + p('b', -j)         # tau_j = b^j x b^-j
t = 'Ba'                                             # t = b^-1 a
rho = 'ABab'                                         # rho = a^-1 b^-1 a b
Xn = lambda n: p('b', -n) + p('a', n)                # X_n = b^-n a^n
conj = lambda u, h: inv(h) + u + h                   # u^h = h^-1 u h


def psi(w):
    img = {'a': 'aa', 'b': 'bb', 'x': comm('aa', 'bb')}
    img.update({INV[k]: inv(v) for k, v in list(img.items())})
    return ''.join(img[c] for c in w)


def subst(word_in_t_rho, u, v):
    """Substitute t -> u, rho -> v in a word over the symbols t, T, r, R."""
    m = {'t': u, 'T': inv(u), 'r': v, 'R': inv(v)}
    return ''.join(m[c] for c in word_in_t_rho)


def sym_inv(w):
    m = {'t': 'T', 'T': 't', 'r': 'R', 'R': 'r'}
    return ''.join(m[c] for c in reversed(w))


def sym_subst(w, u, v):
    m = {'t': u, 'T': sym_inv(u), 'r': v, 'R': sym_inv(v)}
    return ''.join(m[c] for c in w)


RP_sym = 'trTrtrT'                                   # R' = t rho t^-1 rho t rho t^-1
R_sym = 'T' + RP_sym + sym_subst(RP_sym, 'tr', RP_sym) + 'tr' + RP_sym   # R = t^-1 R' R'(t rho, R') t rho R'


def W_sym(n):
    """W_1 = t, W_2n = W_n(t rho t, R), W_2n+1 = W_2n(t rho, R') t, as a symbol word."""
    if n == 1:
        return 't'
    if n % 2 == 0:
        w = W_sym(n // 2)
        img = {'t': 'trt', 'r': R_sym}
    else:
        w = W_sym(n - 1)
        img = {'t': 'tr', 'r': RP_sym}
    img['T'] = sym_inv(img['t'])
    img['R'] = sym_inv(img['r'])
    out = ''.join(img[c] for c in w)
    return out + ('t' if n % 2 == 1 else '')


def letters(sym):
    return subst(sym, t, rho)


def target(name):
    m = re.fullmatch(r'A\((\d+)\)(/via-U)?', name)
    if m:
        return comm(sigma(0), sigma(int(m.group(1))))
    m = re.fullmatch(r'E\((\d+)\)', name)
    if m:
        return comm(sigma(int(m.group(1))), t)
    m = re.fullmatch(r'U\((\d+)\)', name)
    if m:
        j = int(m.group(1))
        return tau(j) + inv(sigma(j))
    m = re.fullmatch(r'B\((\d+)\)', name)
    if m:
        return comm(sigma(-int(m.group(1))), 'b')
    m = re.fullmatch(r'X_(\d+)=W_(\d+)', name)
    if m:
        n = int(m.group(1))
        return Xn(n) + inv(letters(W_sym(n)))
    m = re.fullmatch(r'\[x,X_(\d+)\]', name)
    if m:
        return comm('x', Xn(int(m.group(1))))
    m = re.fullmatch(r'psi\(r(\d)\)', name)
    if m:
        return psi(REL['r' + m.group(1)])
    Pi = sigma(1) + sigma(2) + sigma(0) + sigma(1)
    fixed = {
        'B0': comm('x', sigma(1) + sigma(0) + 'b'),
        'N4': conj(rho, 'b') + inv(letters(RP_sym)),
        '[x,rho]': comm('x', rho),
        'CONV': psi('x') + inv(Pi),
        'BRAID': sigma(1) + sigma(0) + sigma(1) + inv(sigma(0) + sigma(1) + sigma(0)),
        'psi(rho)=R': psi(rho) + inv(letters(R_sym)),
    }
    return fixed[name]


# The complete inventory of certificates the paper relies on; an archive must contain exactly these.
EXPECTED_NAMES = (
    'A(2)',
    'E(0)',
    'U(1)',
    'E(1)',
    'U(2)',
    'B0',
    'B(2)',
    'A(3)',
    'A(4)',
    'E(2)',
    'U(3)',
    'B(3)',
    'A(5)',
    'A(6)',
    'E(3)',
    'N4',
    '[x,rho]',
    'CONV',
    'BRAID',
    'psi(r1)',
    'psi(r5)',
    'psi(r3)',
    'psi(r2)',
    'psi(r4)',
    'psi(rho)=R',
    'X_1=W_1',
    '[x,X_1]',
    'A(3)/via-U',
    'X_2=W_2',
    '[x,X_2]',
    'A(4)/via-U',
    'X_3=W_3',
    '[x,X_3]',
    'A(5)/via-U',
    'X_4=W_4',
    '[x,X_4]',
    'A(6)/via-U',
    'X_5=W_5',
    '[x,X_5]',
    'A(7)',
)


def verify(path):
    with gzip.open(path, 'rt', encoding='ascii') as f:
        data = json.load(f)
    entries = data.get('certificates', [])
    got = [e.get('name') for e in entries]
    ok = True
    missing = sorted(set(EXPECTED_NAMES) - set(got))
    extra = sorted(set(got) - set(EXPECTED_NAMES))
    duplicates = sorted({nm for nm in got if got.count(nm) > 1})
    if missing or extra or duplicates or len(got) != len(EXPECTED_NAMES):
        print('INVENTORY FAILED: missing %s, unexpected %s, duplicated %s' % (missing, extra, duplicates))
        ok = False
    for e in entries:
        parts = []
        good = True
        for z, r, s in e['cells']:
            if not (r in REL and s in (1, -1) and set(z) <= set(INV)):
                good = False
                break
            parts.append(z + (REL[r] if s == 1 else inv(REL[r])) + inv(z))
        good = good and red(''.join(parts)) == red(target(e['name']))
        ok &= good
        print('%-14s cells %7d   %s' % (e['name'], len(e['cells']), 'VERIFIED' if good else 'FAILED'))
    print('ALL VERIFIED' if ok else 'SOME CERTIFICATE FAILED')
    return ok


if __name__ == '__main__':
    sys.exit(0 if verify(sys.argv[1] if len(sys.argv) > 1 else 'out/certificates.json.gz') else 1)
