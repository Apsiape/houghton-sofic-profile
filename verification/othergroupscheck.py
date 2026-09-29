"""Finite regressions for Proposition "Every separation margin", the lattice-area bound on the Dehn function, and
Baumslag-Solitar groups (Section "Other groups").

Standard library only. Exits 1 on any failure. These are finite checks of the manuscript's identities and
constants; the all-case statements are proved in the manuscript.
"""
from fractions import Fraction as Fr
from itertools import permutations, product
import math
import sys

FAIL = []


def check(ok, name):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------------------------------------------------
# 1. Proposition "Every separation margin": the bracket is at least Delta^2/12 with K = K_Delta.
# ---------------------------------------------------------------------------------------------------------
def h2(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def bracket(K, D):
    a = 3200 / (3 * K * K)
    b = 1936 / (3 * K * K)
    q = min(2 * a / 3, 2 / 3)
    return (max(D - 9 / K, 0) ** 2 - a) / 3 - b / (2 * math.log(2)) - (h2(q) + q)


def certify(K, D):
    """Exact rational lower bound on bracket(K, D) - D^2/12, with ln 2 > 69/100 and
    h2(q) <= q log2(1/q) + q/ln 2, where log2(1/q) is bounded by an integer power comparison."""
    K, D = Fr(K), Fr(D)
    a = Fr(3200, 3) / (K * K)
    b = Fr(1936, 3) / (K * K)
    q = 2 * a / 3
    L = 0
    while Fr(2) ** L < 1 / q:
        L += 1
    ln2 = Fr(69, 100)
    lead = D - 9 / K
    return (lead * lead - a) / 3 - b / (2 * ln2) - (q * L + q / ln2 + q) - D * D / 12


def K_Delta(D):
    return math.sqrt(80000 * (1 + math.log2(1 / D))) / D


ok = True
for D in [Fr(1), Fr(1, 2), Fr(1, 4), Fr(1, 10), Fr(1, 20), Fr(1, 50), Fr(1, 100), Fr(1, 1000)]:
    K = math.ceil(K_Delta(float(D)))
    ok &= certify(K, D) > 0
check(ok, "margin: exact rational bracket >= Delta^2/12 at eight margins, K = ceil(K_Delta)")

worst = min(bracket(K_Delta(2.0 ** -L), 2.0 ** -L) / ((2.0 ** -L) ** 2 / 12)
            for L in [i / 20 for i in range(0, 801)])
check(worst > 1, f"margin: bracket/(Delta^2/12) >= {worst:.3f} > 1 on a grid down to Delta = 2^-40")

Lstar = 1 / math.log(2) - 1
gap = math.log2(1 + Lstar) - Lstar
c0 = 821.2 + 711.2 * (math.log2(2 * math.e * 80000 / 711.2) + 0.1)
chain = (3200 / 9 + 1936 / (6 * math.log(2)) < 821.2 and 6400 / 9 < 711.2 and gap < 0.087 and c0 <= 7476
         and 3 * 711.2 <= 2134 and 7476 <= 5 * 80000 / 48 and 2134 <= 5 * 80000 / 48)
check(chain, f"margin: derivation constants (max log2(1+L)-L = {gap:.4f} < 0.087; {c0:.1f} <= 7476)")

# ---------------------------------------------------------------------------------------------------------
# 2. The lattice-area lower bound on the Dehn function of H_3 (right actions, gh = g then h).
# ---------------------------------------------------------------------------------------------------------
W, FAR = 60, 150


def act(letter, p):
    i, j = p
    if letter in "xX":
        return (1, 2) if p == (1, 1) else (1, 1) if p == (1, 2) else p
    ray = 2 if letter in "aA" else 3
    if letter.islower():
        if i == 1:
            return (ray, 1) if j == 1 else (1, j - 1)
        return (ray, j + 1) if i == ray else p
    if i == ray:
        return (1, 1) if j == 1 else (ray, j - 1)
    return (1, j + 1) if i == 1 else p


def image(word, p):
    for letter in word:
        p = act(letter, p)
    return p


def inv(w):
    return "".join(c.swapcase() for c in reversed(w))


def comm(x, y):
    return x + y + inv(x) + inv(y)


POINTS = [(i, j) for i in (1, 2, 3) for j in range(1, W + 1)] + [(i, FAR) for i in (1, 2, 3)]
rel = {1: "xx", 2: "xaxA" * 3, 3: comm("x", "aaxAA"), 4: "abABX", 5: "axAbXB"}
check(all(all(image(w, p) == p for p in POINTS) for w in rel.values()), "Dehn: the five relators hold")

ok = True
for m in range(1, 26):
    target = {}
    for j in range(1, m + 1):
        target[(1, j)], target[(1, m + j)] = (1, m + j), (1, j)
    ok &= all(image(comm("a" * m, "b" * m), p) == target.get(p, p) for p in POINTS)
check(ok, "Dehn: [a^m,b^m] is a product of m disjoint transpositions, m = 1..25")


def signed_area(word):
    x = y = twice = 0
    for c in word:
        dx, dy = {"a": (1, 0), "A": (-1, 0), "b": (0, 1), "B": (0, -1)}.get(c, (0, 0))
        twice += x * dy - y * dx
        x, y = x + dx, y + dy
    assert (x, y) == (0, 0)
    return Fr(twice, 2)


check(tuple(signed_area(rel[i]) for i in range(1, 6)) == (0, 0, 0, 1, 0), "Dehn: relator areas (0,0,0,1,0)")
check(all(signed_area(comm("a" * m, "b" * m) * 2) == 2 * m * m for m in range(1, 26)),
      "Dehn: [a^m,b^m]^2 has length 8m and encloses area 2m^2")

# ---------------------------------------------------------------------------------------------------------
# 3. Baumslag-Solitar tiles (right actions). Theorem "bs" (a).
# ---------------------------------------------------------------------------------------------------------
def tiles(step, count_res, arcs, size, ell):
    """Tiles along the cycles of x -> x + step on Z/size: one cycle per residue mod count_res, cut into arcs."""
    out = []
    for r in range(count_res):
        cyc, x = [], r
        for _ in range(size // count_res):
            cyc.append(x)
            x = (x + step) % size
        assert x == r
        for b in range(arcs):
            out.append(cyc[b * ell:(b + 1) * ell])
    return out


def mat_mul(A, B):
    return ((A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]),
            (A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]))


def mat_pow(A, e):
    R = ((1, 0), (0, 1))
    B = A if e >= 0 else ((A[1][1], -A[0][1]), (-A[1][0], A[0][0]))
    for _ in range(abs(e)):
        R = mat_mul(R, B)
    return R


U, Vm = ((1, 2), (0, 1)), ((1, 0), (2, 1))
IDENT = ((1, 0), (0, 1))

bs_ok, trajectories = True, 0
for m, n, ell in [(2, 3, 3), (3, 2, 3), (-2, 3, 3), (2, -3, 2), (-2, -3, 2), (2, 4, 2), (4, 6, 2), (3, 5, 2)]:
    M, N = abs(m), abs(n)
    d = M * N
    size = d * ell
    P = tiles(m % size, M, N, size, ell)
    Q = tiles(n % size, N, M, size, ell)
    assert len(P) == len(Q) == d
    ptile = {x: i for i, t in enumerate(P) for x in t}
    qtile = {x: i for i, t in enumerate(Q) for x in t}
    Tmap = {Q[i][k]: P[i][k] for i in range(d) for k in range(ell)}
    Tinv = {v: k for k, v in Tmap.items()}
    Cm = {P[i][k]: P[i][(k + 1) % ell] for i in range(d) for k in range(ell)}
    Cn = {Q[i][k]: Q[i][(k + 1) % ell] for i in range(d) for k in range(ell)}
    bs_ok &= all(Tinv[Cm[Tmap[x]]] == Cn[x] for x in range(size))
    bs_ok &= sum(Cm[x] != (x + m) % size for x in range(size)) == d
    bs_ok &= sum(Cn[x] != (x + n) % size for x in range(size)) == d

    def relator_moves(x):
        i = qtile[x]
        y = (Tmap[x] + m) % size
        return Tinv[y] != (x + n) % size or ptile[y] != i

    bs_ok &= sum(relator_moves(x) for x in range(size)) <= 2 * d
    S = [mat_mul(mat_mul(mat_pow(U, i + 1), Vm), mat_pow(U, -(i + 1))) for i in range(d)]
    K = 2 * max(M, N) + 1
    for j in (1, 2, 3):
        Kj = K if j < 3 else max(M, N)
        for eps in product((1, -1), repeat=j):
            for ks in product(range(-Kj, Kj + 1), repeat=j + 1):
                if any((eps[i], eps[i + 1]) == (1, -1) and ks[i + 1] % M == 0 or
                       (eps[i], eps[i + 1]) == (-1, 1) and ks[i + 1] % N == 0 for i in range(j - 1)):
                    continue
                for x0 in range(size):
                    x, aux = (x0 + ks[0]) % size, []
                    for i in range(j):
                        if eps[i] == 1:
                            aux.append((qtile[x], 1))
                            x = Tmap[x]
                        else:
                            aux.append((ptile[x], -1))
                            x = Tinv[x]
                        x = (x + ks[i + 1]) % size
                    trajectories += 1
                    if any(aux[i][0] == aux[i + 1][0] and aux[i][1] == -aux[i + 1][1] for i in range(j - 1)):
                        bs_ok = False
                    g = IDENT
                    for i, e in aux:
                        g = mat_mul(g, mat_pow(S[i], e))
                    if g == IDENT:
                        bs_ok = False
check(bs_ok, f"BS tiles: T C_m T^-1 = C_n, cut defects 1/l, relator defect <= 2/l, and {trajectories} "
             "reduced-word trajectories with reduced, nontrivial auxiliary words (8 parameter sets)")

# ---------------------------------------------------------------------------------------------------------
# 4. BS(2,3): [t a t^-1, a] dies in every homomorphism to S_5 and S_6.
# ---------------------------------------------------------------------------------------------------------
def compose(p, q):
    return tuple(q[p[i]] for i in range(len(p)))


def pinv(p):
    r = [0] * len(p)
    for i, v in enumerate(p):
        r[v] = i
    return tuple(r)


ok, homs = True, 0
for deg in (5, 6):
    G = list(permutations(range(deg)))
    for a in G:
        a2, a3 = compose(a, a), compose(compose(a, a), a)
        ai = pinv(a)
        for t in G:
            ti = pinv(t)
            if compose(compose(t, a2), ti) != a3:
                continue
            homs += 1
            x = compose(compose(t, a), ti)
            ok &= compose(compose(compose(x, a), pinv(x)), ai) == tuple(range(deg))
check(ok, f"BS(2,3): [t a t^-1, a] is trivial in all {homs} homomorphisms to S_5 and S_6")

print("\nall checks passed" if not FAIL else f"\nFAILED: {FAIL}")
sys.exit(1 if FAIL else 0)
