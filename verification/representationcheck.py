"""Exact finite regressions for the parity quotient and Clifford images.

Uses monomial matrices encoded by permutations and powers of i, not floating
point arithmetic. These samples do not prove the all-m representation theorem.
"""
from itertools import product


def ray_action(point, word):
    ray, height = point
    for generator, sign in word:
        target = generator + 2
        if sign == 1:
            if ray == 1:
                if height == 1:
                    ray = target
                else:
                    height -= 1
            elif ray == target:
                height += 1
        else:
            if ray == target:
                if height == 1:
                    ray = 1
                else:
                    height -= 1
            elif ray == 1:
                height += 1
    return ray, height


def multiply(a, b):
    """Matrix product a b, acting on column basis vectors."""
    pa, za = a
    pb, zb = b
    return (tuple(pa[j] for j in pb),
            tuple((zb[i] + za[pb[i]]) % 4 for i in range(len(pb))))


def phase(a, power):
    return a[0], tuple((z + power) % 4 for z in a[1])


def clifford(d):
    r = d // 2
    size = 1 << r
    matrices = []
    for j in range(r):
        permutation = tuple(x ^ (1 << j) for x in range(size))
        prefix = [((x & ((1 << j) - 1)).bit_count() % 2) for x in range(size)]
        matrices.append((permutation, tuple(2 * p for p in prefix)))
        matrices.append((permutation, tuple((1 + 2 * (p + ((x >> j) & 1))) % 4
                                            for x, p in enumerate(prefix))))
    if d % 2:
        matrices.append((tuple(range(size)), tuple(2 * (x.bit_count() % 2)
                                                  for x in range(size))))
    return matrices


def binary_rank(rows):
    pivots = {}
    for value in rows:
        while value:
            bit = value.bit_length() - 1
            if bit in pivots:
                value ^= pivots[bit]
            else:
                pivots[bit] = value
                break
    return len(pivots)


ray_checks = pair_checks = 0
for d in range(2, 11):
    r = d // 2
    for i in range(d):
        for j in range(i + 1, d):
            word = [(i, 1), (j, 1), (i, -1), (j, -1)]
            # A four-letter word cannot bring a height above five to a ray tip.
            for ray, height in product(range(1, d + 2), range(1, 7)):
                expected = (1, 3 - height) if ray == 1 and height <= 2 else (ray, height)
                assert ray_action((ray, height), word) == expected
                ray_checks += 1
    matrices = clifford(d)
    size = 1 << r
    identity = (tuple(range(size)), (0,) * size)
    for a in matrices:
        assert multiply(a, a) == identity
    for i in range(d):
        for j in range(i + 1, d):
            assert multiply(matrices[i], matrices[j]) == phase(multiply(matrices[j], matrices[i]), 2)
            pair_checks += 1
    h = [phase(multiply(matrices[2*j], matrices[2*j+1]), 1) for j in range(r)]
    assert all(a[0] == identity[0] and set(a[1]) <= {0, 2} for a in h)
    patterns = [tuple(a[1][x] for a in h) for x in range(size)]
    assert len(set(patterns)) == size
    for j in range(r):
        for x in range(size):
            y = matrices[2*j][0][x]
            assert patterns[y] == tuple((z + (2 if k == j else 0)) % 4
                                        for k, z in enumerate(patterns[x]))
    assert binary_rank([((1 << d) - 1) ^ (1 << i) for i in range(d)]) == 2 * r

print(f"Parity commutators: {ray_checks} exact ray checks; Clifford images: {pair_checks} pairs, d=2..10.")
print("Exact finite regressions only; the all-m quotient, irreducibility and index proof is in the manuscript.")
