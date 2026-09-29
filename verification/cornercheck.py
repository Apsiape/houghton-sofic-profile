"""Finite regressions for Proposition "Corner models" (Section "Upper bounds"), which Proposition "Quadratic lower
bound" and the upper bounds use.

For each M, the colour permutations A_{i,j}, B_{i,j}, D_i are built from the manuscript's formulas and every word is
followed clock by clock. Checked at M = 5,...,16: r_1, r_2, r_3, r_5 act trivially at every clock; r_4 acts trivially
except at the clock (M-1, M-1), where it acts as R_M; gamma acts as a three-cycle at every clock; at every clock with
i + j >= M + 3, sigma_{2M-1} acts as the transposition (1, 2M+3-i-j) and C_{2M-1} as a three-cycle, at exactly
(M-4)(M-3)/2 clocks. A negative control drops tau from the recursion for D_i and must break r_4 off the corner.

Standard library only. Exits 1 on any failure. The all-M statement is proved in the manuscript.
"""
import sys

FAIL = []


def check(ok, name):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAIL.append(name)


def model(M, with_tau=True):
    l = 2 * M + 2
    L = 3 * l
    ident = tuple(range(L + 1))  # index 0 unused; p[t] is the image of t

    def mul(p, q):  # p, then q
        return tuple(q[p[t]] for t in range(L + 1))

    def inv(p):
        r = [0] * (L + 1)
        for t in range(L + 1):
            r[p[t]] = t
        return tuple(r)

    def c(r):  # reverse cycle (1 r r-1 ... 2)
        p = list(range(L + 1))
        p[1] = r
        for t in range(2, r + 1):
            p[t] = t - 1
        return tuple(p)

    tau = list(range(L + 1))
    tau[1], tau[2] = 2, 1
    tau = tuple(tau)
    D = [c(2 * l - M + 1)]
    for i in range(M - 1):
        mid = tau if with_tau else ident
        D.append(mul(mul(mul(inv(c(l - i - (M - 1))), mid), D[i]), c(l - i)))

    def A(i, j):
        return c(l - i - j)

    def B(i, j):
        return D[i] if j == M - 1 else c(2 * l - j)

    def walk(word, i, j):
        P = ident
        for ch in word:
            if ch == "a":
                P = mul(P, A(i, j)); i = (i + 1) % M
            elif ch == "A":
                i = (i - 1) % M; P = mul(P, inv(A(i, j)))
            elif ch == "b":
                P = mul(P, B(i, j)); j = (j + 1) % M
            elif ch == "B":
                j = (j - 1) % M; P = mul(P, inv(B(i, j)))
            elif ch in "xX":
                P = mul(P, tau)
        return (i, j), P

    R = list(range(L + 1))
    R[1], R[M + 4] = M + 4, 1
    for t in range(5, M + 4):
        R[t], R[t + M] = t + M, t
    return L, ident, walk, tuple(R)


def inverse_word(w):
    return "".join(ch.swapcase() for ch in reversed(w))


def comm(x, y):
    return x + y + inverse_word(x) + inverse_word(y)


def moved(P, L):
    return [t for t in range(1, L + 1) if P[t] != t]


RELATORS = {1: "xx", 2: "xaxA" * 3, 3: comm("x", "aaxAA"), 4: "abABX", 5: "axAbXB"}

for M in range(5, 17):
    L, ident, walk, RM = model(M)
    clocks = [(i, j) for i in range(M) for j in range(M)]
    ok = True
    for (i, j) in clocks:
        for k, w in RELATORS.items():
            end, P = walk(w, i, j)
            want = RM if (k == 4 and (i, j) == (M - 1, M - 1)) else ident
            ok &= end == (i, j) and P == want
    check(ok, f"M={M}: r1,r2,r3,r5 trivial at all clocks; r4 = R_M at (M-1,M-1) only")
    check(all(len(moved(walk("xaxA", i, j)[1], L)) == 3 for (i, j) in clocks),
          f"M={M}: gamma is a three-cycle at every clock")
    k = 2 * M - 1
    sigma = "a" * k + "x" + "A" * k
    Ck = comm("x", sigma)
    good = [(i, j) for (i, j) in clocks if i + j >= M + 3]
    ok = len(good) == (M - 4) * (M - 3) // 2
    for (i, j) in good:
        _, S = walk(sigma, i, j)
        _, C = walk(Ck, i, j)
        ok &= moved(S, L) == sorted([1, 2 * M + 3 - i - j]) and len(moved(C, L)) == 3
    check(ok, f"M={M}: sigma_(2M-1) = (1, 2M+3-i-j) and C_(2M-1) a three-cycle at all (M-4)(M-3)/2 clocks i+j >= M+3")

L, ident, walk, RM = model(8, with_tau=False)
broken = sum(1 for i in range(8) for j in range(8)
             if (i, j) != (7, 7) and walk(RELATORS[4], i, j)[1] != ident)
check(broken > 0, f"negative control: without tau in the D-recursion r4 fails at {broken} further clocks (M=8)")

print("\nall checks passed" if not FAIL else f"\nFAILED: {FAIL}")
sys.exit(1 if FAIL else 0)
