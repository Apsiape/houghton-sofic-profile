"""Van Kampen certificates for Johnson's presentation of Houghton's group H_3.

Letters: a, b, x (= alpha); inverses A, B, X.
Presentation P = < a, b, x | r1..r5 >:
  r1 = x^2
  r2 = (x a x a^-1)^3
  r3 = [x, a^2 x a^-2]        with [u,v] = u v u^-1 v^-1
  r4 = a b a^-1 b^-1 x^-1
  r5 = a x a^-1 b x^-1 b^-1

A certificate for a null word w is a list of cells (z, r, s) with
      w  ==  prod_k  z_k r_k^{s_k} z_k^{-1}      (equality in the free group).
Its length is an upper bound on Area_P(w).

A derivation rewrites a list of tokens (each token a word).  Every step
replaces one contiguous run u of tokens by a run v, where u v^-1 is conjugate in
the free group to J^{+1} or J^{-1} for a previously certified null word J; the
step appends J's cells, conjugated into place.  Free steps (cost 0) replace the
whole token list by a freely equal one.  When the token list reduces to the
empty word, the accumulated cells form a certificate for the target, which is
re-verified from scratch by free reduction.
"""

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


def cyc(w):
    """w reduced -> (s, core) with w == s core s^-1 freely and core cyclically reduced."""
    w = red(w)
    i = 0
    n = len(w)
    while i < n - 1 - i and w[i] == INV[w[n - 1 - i]]:
        i += 1
    return w[:i], w[i:n - i]


RELATORS = {
    'r1': 'xx',
    'r2': 'xaxA' * 3,
    'r3': 'x' + 'aaxAA' + 'X' + 'aaXAA',
    'r4': 'abABX',
    'r5': 'axAbXB',
}


def conj_find(w, J):
    """Return (c, e) with red(c J^e c^-1) == red(w), e in {+1,-1}, or None."""
    s, w0 = cyc(w)
    if w0 == '':
        return None
    for e in (1, -1):
        Je = J if e == 1 else inv(J)
        t, J0 = cyc(Je)          # Je == t J0 t^-1
        if len(J0) != len(w0):
            continue
        dbl = J0 + J0
        k = dbl.find(w0)
        while k != -1 and k < len(J0):
            # w0 == J0[k:] + J0[:k] == p^-1 J0 p with p = J0[:k]
            p = J0[:k]
            c = red(s + inv(p) + inv(t))
            if red(c + Je + inv(c)) == red(w):
                return c, e
            k = dbl.find(w0, k + 1)
    return None


class Lemma:
    def __init__(self, name, word, cells, note=''):
        self.name = name
        self.word = red(word)
        self.cells = cells          # list of (z, r, s)
        self.note = note

    @property
    def cost(self):
        return len(self.cells)

    def cells_signed(self, e):
        if e == 1:
            return list(self.cells)
        return [(z, r, -s) for (z, r, s) in reversed(self.cells)]


def expand(cells):
    out = []
    for z, r, s in cells:
        R = RELATORS[r] if s == 1 else inv(RELATORS[r])
        out.append(z + R + inv(z))
    return red(''.join(out))


def check_cert(word, cells):
    return expand(cells) == red(word)


REL = {k: Lemma(k, v, [('', k, 1)]) for k, v in RELATORS.items()}


class Deriv:
    def __init__(self, name, tokens):
        self.name = name
        self.T = red(''.join(tokens))
        self.cur = list(tokens)
        self.O = ''
        self.cells = []
        self.steps = []

    def word(self):
        return ''.join(self.cur)

    def free(self, new):
        new = list(new)
        if red(''.join(new)) != red(self.word()):
            raise AssertionError('%s: free step changes the element:\n  %s\n->%s' % (
                self.name, red(self.word()), red(''.join(new))))
        self.cur = new

    def rotate(self, k):
        p = ''.join(self.cur[:k])
        self.cur = self.cur[k:] + self.cur[:k]
        self.O = self.O + p

    def step(self, new, lemma, label=''):
        """Replace the current token list by `new`, which must differ from it in one
        contiguous run; the run's change must be a conjugate of lemma^{+-1}."""
        new = list(new)
        old = self.cur
        i = 0
        while i < len(old) and i < len(new) and old[i] == new[i]:
            i += 1
        j = 0
        while (j < len(old) - i and j < len(new) - i
               and old[len(old) - 1 - j] == new[len(new) - 1 - j]):
            j += 1
        u = ''.join(old[i:len(old) - j])
        v = ''.join(new[i:len(new) - j])
        self.apply_run(i, len(old) - j, new[i:len(new) - j], lemma, label, u, v)

    def apply_run(self, i, j, repl, lemma, label='', u=None, v=None):
        if u is None:
            u = ''.join(self.cur[i:j])
        if v is None:
            v = ''.join(repl)
        w = u + inv(v)
        if red(w) == '':            # freely trivial replacement: no cells needed
            self.cur = self.cur[:i] + list(repl) + self.cur[j:]
            self.steps.append(((label or lemma.name) + ' (free)', 0))
            return
        f = conj_find(w, lemma.word)
        if f is None:
            raise AssertionError('%s: step %s is not a conjugate of %s^{+-1}:\n  u=%s\n  v=%s\n  uv^-1=%s\n  J=%s' % (
                self.name, label, lemma.name, u, v, red(w), lemma.word))
        c, e = f
        x = ''.join(self.cur[:i])
        pre = self.O + x + c
        for z, r, s in lemma.cells_signed(e):
            self.cells.append((red(pre + z), r, s))
        self.cur = self.cur[:i] + list(repl) + self.cur[j:]
        self.steps.append((label or lemma.name, lemma.cost))

    def sub(self, pattern, repl, lemma, label='', occurrence=0):
        """Replace the `occurrence`-th occurrence of the token run `pattern`."""
        pattern = list(pattern)
        n = len(pattern)
        found = -1
        cnt = 0
        for i in range(len(self.cur) - n + 1):
            if self.cur[i:i + n] == pattern:
                if cnt == occurrence:
                    found = i
                    break
                cnt += 1
        if found < 0:
            raise AssertionError('%s: pattern %s not found (occurrence %d) in %s' % (
                self.name, pattern, occurrence, self.cur))
        self.apply_run(found, found + n, repl, lemma, label)

    def done(self, note=''):
        if red(self.word()) != '':
            raise AssertionError('%s: not reduced to the empty word: %s' % (self.name, red(self.word())))
        if not check_cert(self.T, self.cells):
            raise AssertionError('%s: flattened certificate does not reproduce the target' % self.name)
        return Lemma(self.name, self.T, self.cells, note)


# ---------------------------------------------------------------- words

def apow(k):
    return 'a' * k if k >= 0 else 'A' * (-k)


def bpow(k):
    return 'b' * k if k >= 0 else 'B' * (-k)


def S(j):
    """sigma_j = a^j x a^-j"""
    return red(apow(j) + 'x' + apow(-j))


def Si(j):
    return inv(S(j))


def TAU(j):
    return red(bpow(j) + 'x' + bpow(-j))


t_ = 'Ba'          # t = b^-1 a
ti_ = 'Ab'
rho_ = 'ABab'      # rho = a^-1 b^-1 a b
rhoi_ = 'BAba'


def Tk(k):
    """t_k = a^k t a^-k"""
    return red(apow(k) + t_ + apow(-k))


def comm(u, v):
    return red(u + v + inv(u) + inv(v))


def conjw(u, h):
    """u^h = h^-1 u h"""
    return red(inv(h) + u + h)


PSI = {'a': 'aa', 'A': 'AA', 'b': 'bb', 'B': 'BB'}
W_ALPHA = 'aabbAABB'           # psi(alpha) = [a^2, b^2]
PSI['x'] = W_ALPHA
PSI['X'] = inv(W_ALPHA)


def psi(w):
    return ''.join(PSI[c] for c in w)


def psi_cells(cells, psi_rel):
    """Transport a certificate through psi, replacing psi(r_i) by its certificate."""
    out = []
    for z, r, s in cells:
        pz = psi(z)
        for zz, rr, ss in psi_rel[r].cells_signed(s):
            out.append((red(pz + zz), rr, ss))
    return out
