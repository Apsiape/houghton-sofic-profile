"""Finite regression checks for buffered collection and Coxeter insertion.

This checks local rewrites, not the all-word area theorem or Johnson's theorem.
The general cost and normal-form arguments are proved in the manuscript.
"""
if not __debug__:
    raise SystemExit("This check uses assert statements; run it without python -O.")
from random import Random

INV = dict(zip("aAbBxX", "AaBbXx"))

def inverse(w):
    return "".join(INV[c] for c in reversed(w))

def sigma(j):
    assert j >= 0
    return "a" * j + "x" + "A" * j

def action(point, word):
    ray, j = point
    for c in word:
        if c in "xX":
            if ray == 1 and j <= 2:
                j = 3 - j
        else:
            target = 2 if c in "aA" else 3
            if c in "ab":
                if ray == 1:
                    if j == 1: ray = target
                    else: j -= 1
                elif ray == target: j += 1
            else:
                if ray == target:
                    if j == 1: ray = 1
                    else: j -= 1
                elif ray == 1: j += 1
    return ray, j

def equal_actions(u, v):
    # At heights above length+1 no alpha/transfer can act. Include one tail
    # point as well, so this finite comparison determines these ray actions.
    cutoff = max(len(u), len(v)) + 2
    return all(action((r, j), u) == action((r, j), v)
               for r in (1, 2, 3) for j in range(1, cutoff + 1))

collections = 0
for m in range(7):
    for q in range(7):
        section = "a" * m + "b" * q
        rules = {
            "a": "".join(inverse(sigma(j)) for j in range(m+q-1, m-1, -1))
                 + "a" * (m+1) + "b" * q,
            "x": sigma(m+q) + section,
            "X": inverse(sigma(m+q)) + section,
            "b": "a" * m + "b" * (q+1),
        }
        if m:
            rules["A"] = "".join(sigma(j) for j in range(m-1, m+q-1)) + "a" * (m-1) + "b" * q
        if q:
            rules["B"] = "a" * m + "b" * (q-1)
        for letter, target in rules.items():
            assert equal_actions(section + letter, target), (m, q, letter)
            collections += 1

def far_area_bound(gap):
    """Certified manuscript input; not inferred from permutation equality."""
    assert gap >= 2
    return gap**11


def insertion_rule(d, k, i):
    c = list(range(d-1, k-1, -1))
    word = c + [i]
    moves = cells = 0
    def swap(p):
        nonlocal moves, cells
        gap = abs(word[p] - word[p+1])
        assert gap >= 2
        cells += far_area_bound(gap)
        word[p], word[p+1] = word[p+1], word[p]
        moves += 1
    if i <= k-2:
        for p in range(len(c)-1, -1, -1): swap(p)
        target, carry, next_k = [i] + c, i, k
    elif i == k-1:
        target, carry, next_k = list(range(d-1, k-2, -1)), None, k-1
    elif i == k:
        assert word[-2:] == [i, i]
        del word[-2:]
        moves += 1
        cells += 1  # One conjugate of alpha^2.
        target, carry, next_k = list(range(d-1, k, -1)), None, k+1
    else:
        p = len(word)-1
        while word[p-1] <= i-2:
            swap(p-1)
            p -= 1
        assert word[p-2:p+1] == [i, i-1, i]
        word[p-2:p+1] = [i-1, i, i-1]
        moves += 1
        cells += 4  # One cubic relator and three square cells.
        p -= 2
        while p:
            swap(p-1)
            p -= 1
        target, carry, next_k = [i-1] + c, i-1, k
    assert word == target and moves <= d+1, (d, k, i, word, target)
    assert cells <= 4 * (1 + far_area_bound(max(2, d+1))) * moves
    return carry, next_k, moves, cells

rules = 0
for d in range(1, 25):
    for k in range(d+1):
        for i in range(d):
            insertion_rule(d, k, i)
            rules += 1

def insert(nf, d, i):
    carry, k, count, cells = insertion_rule(d, nf[-1], i)
    lower = nf[:-1]
    if carry is not None:
        lower, subcount, subcells = insert(lower, d-1, carry)
        count += subcount
        cells += subcells
    assert count <= d * (d+1)
    assert cells <= 4 * (1 + far_area_bound(max(2, d+1))) * d * (d+1)
    return lower + [k], count, cells

def nf_word(nf):
    return [i for d, k in enumerate(nf, 1) for i in range(d-1, k-1, -1)]

def perm(word, d):
    values = list(range(d+1))
    for i in word:
        values = [i+1 if x == i else i if x == i+1 else x for x in values]
    return values

rng = Random(130)
for d in range(1, 13):
    for _ in range(10):
        word = [rng.randrange(d) for _ in range(40)]
        word += word[::-1]  # Exact null word; no inverse signs for involutions.
        nf = list(range(1, d+1))
        for end, letter in enumerate(word, 1):
            nf, _, _ = insert(nf, d, letter)
            assert perm(nf_word(nf), d) == perm(word[:end], d)
        assert nf_word(nf) == []


def buffered_cost_check(word):
    """Accumulate charged rules for a supplied null word, including inverses.

    Uses U(q) <= F*q^2 and the certified far-area input; does not derive either
    premise from these finite computations.
    """
    assert equal_actions(word, "")
    n = len(word)
    assert n > 0
    F = 1 + far_area_bound(4*n+2)
    m = q = n
    collected, trace = [], []
    collection_cost = 0
    for letter in word:
        if letter == "a":
            added = [(j, -1) for j in range(m+q-1, m-1, -1)]
            charge = q + sum(F*j*j for j in range(q))
            m += 1
        elif letter == "A":
            added = [(j, 1) for j in range(m-1, m+q-1)]
            charge = q + sum(F*j*j for j in range(q))
            m -= 1
        elif letter in "xX":
            added = [(m+q, 1 if letter == "x" else -1)]
            charge = F*q*q
        else:
            added, charge = [], 0
            q += 1 if letter == "b" else -1
        collected.extend(added)
        collection_cost += charge
        trace.append((letter, m, q, added))
        assert 0 <= m <= 2*n and 0 <= q <= 2*n
    assert (m, q) == (n, n)
    assert len(collected) <= 2*n*n+n
    assert all(0 <= j <= 4*n for j, sign in collected)
    assert collection_cost <= 5*F*n**4
    inverse_cost = sum(sign < 0 for _, sign in collected)
    nf, insertion_cost, d = list(range(1, 4*n+2)), 0, 4*n+1
    for j, _ in collected:
        nf, _, charge = insert(nf, d, j)
        insertion_cost += charge
    assert nf_word(nf) == []
    assert insertion_cost <= 360*F*n**4
    assert collection_cost + inverse_cost + insertion_cost <= 400*F*n**4
    return trace


trace = buffered_cost_check("abABX")
assert [(m, q) for _, m, q, _ in trace] == [(6, 5), (6, 6), (5, 6), (5, 5), (5, 5)]
assert trace[0][3] == [(j, -1) for j in range(9, 4, -1)]
assert trace[2][3] == [(j, 1) for j in range(5, 11)]
for relator in ("xx", "xa xA".replace(" ", "") * 3,
                "xaa xAA Xaa XAA".replace(" ", ""), "axAbXB"):
    buffered_cost_check(relator)

print(f"Collection: {collections} finite ray-action identities; Coxeter: {rules} locally checked rewrite sequences.")
print("Recursive insertion tested on 120 null words, with every intermediate permutation checked.")
print("Original-cell costs checked, including five buffered relator traces and the 400*n^4*F bound.")
