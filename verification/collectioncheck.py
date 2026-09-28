"""Finite regression checks for buffered collection and Coxeter insertion.

This checks local rewrites, not the all-word area theorem or Johnson's theorem.
The general cost and normal-form arguments are proved in the manuscript.
"""
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

def insertion_rule(d, k, i):
    c = list(range(d-1, k-1, -1))
    word = c + [i]
    moves = 0
    def swap(p):
        nonlocal moves
        assert abs(word[p] - word[p+1]) >= 2
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
        target, carry, next_k = list(range(d-1, k, -1)), None, k+1
    else:
        p = len(word)-1
        while word[p-1] <= i-2:
            swap(p-1)
            p -= 1
        assert word[p-2:p+1] == [i, i-1, i]
        word[p-2:p+1] = [i-1, i, i-1]
        moves += 1
        p -= 2
        while p:
            swap(p-1)
            p -= 1
        target, carry, next_k = [i-1] + c, i-1, k
    assert word == target and moves <= d+1, (d, k, i, word, target)
    return carry, next_k, moves

rules = 0
for d in range(1, 25):
    for k in range(d+1):
        for i in range(d):
            insertion_rule(d, k, i)
            rules += 1

def insert(nf, d, i):
    carry, k, count = insertion_rule(d, nf[-1], i)
    lower = nf[:-1]
    if carry is not None:
        lower, subcount = insert(lower, d-1, carry)
        count += subcount
    assert count <= (d+1)**2
    return lower + [k], count

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
            nf, _ = insert(nf, d, letter)
            assert perm(nf_word(nf), d) == perm(word[:end], d)
        assert nf_word(nf) == []

print(f"Collection: {collections} finite ray-action identities; Coxeter: {rules} locally checked rewrite sequences.")
print("Recursive insertion tested on 120 null words, with every intermediate permutation checked.")
