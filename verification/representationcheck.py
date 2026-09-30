"""Exact finite regressions for the parity quotient and Clifford images.

Uses monomial matrices encoded by permutations and powers of i, not floating
point arithmetic. These samples do not prove the all-m representation theorem.
"""
if not __debug__:
    raise SystemExit("This check uses assert statements; run it without python -O.")
from itertools import permutations, product


def right_product(*perms):
    """Permutation product in the manuscript's right-action convention."""
    result = tuple(range(len(perms[0])))
    for perm in perms:
        result = tuple(perm[x] for x in result)
    return result


def inverse(perm):
    result = [0] * len(perm)
    for i, x in enumerate(perm):
        result[x] = i
    return tuple(result)


def cycle(size, *points):
    result = list(range(size))
    for x, y in zip(points, points[1:] + points[:1]):
        result[x] = y
    return tuple(result)


def parity(perm):
    return sum(x > y for i, x in enumerate(perm) for y in perm[i+1:]) % 2


def normal_subgroup_regressions():
    """Finite identities only; the infinite normal-subgroup argument is written."""
    commutators = centralizers = inverse_controls = 0
    for head in permutations(range(6)):
        x = head + (6, 7)
        if x == tuple(range(8)):
            continue
        p = next(i for i in range(6) if x[i] != i)
        q = inverse(x)[p]
        c = cycle(8, p, 6, 7)
        comm = right_product(x, c, inverse(x), inverse(c))
        expected = cycle(8, q, p, 7)
        assert comm == expected
        commutators += 1
        # Reversing the claimed cycle must not pass unnoticed.
        assert comm != inverse(expected)
        inverse_controls += 1

        r, s = [i for i in range(8) if i not in (p, q)][:2]
        c = cycle(8, p, r, s)
        conjugate = right_product(x, c, inverse(x))
        assert c[q] == q and conjugate[q] != q
        centralizers += 1

    conjugators = 0
    for target in permutations(range(8), 3):
        z = [None] * 8
        for i, point in enumerate(target):
            z[point] = i
        unused = [i for i in range(8) if i not in target]
        for point, image in zip(unused, range(3, 8)):
            z[point] = image
        if parity(z):
            a, b = unused[:2]
            z[a], z[b] = z[b], z[a]
        assert parity(z) == 0
        assert right_product(z, cycle(8, 0, 1, 2), inverse(z)) == cycle(8, *target)
        conjugators += 1
    print(f"Normal-subgroup identities: {commutators} commutators, "
          f"{centralizers} centralizer witnesses, {conjugators} even conjugators; "
          f"{inverse_controls} inverse-cycle negative controls rejected.")


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

normal_subgroup_regressions()
print(f"Parity commutators: {ray_checks} exact ray checks; Clifford images: {pair_checks} pairs, d=2..10.")
print("Exact finite regressions only; the all-m quotient, irreducibility and index proof is in the manuscript.")
