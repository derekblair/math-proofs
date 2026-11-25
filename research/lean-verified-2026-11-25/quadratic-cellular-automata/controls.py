"""Independent small-case checks. The Lean proof does not depend on these."""
from itertools import combinations


def shift(x, n):
    return (x >> 1) | ((x & 1) << (n - 1))


def d(x, n):
    return x ^ shift(x, n)


def apply(table, x, n, k):
    mask = (1 << k) - 1
    y = 0
    for i in range(n):
        y |= table[x & mask] << i
        x = shift(x, n)
    return y


def integrate(x, n):
    y, prev = 0, 0
    for i in range(2*n):
        y |= prev << i
        prev ^= (x >> (i % n)) & 1
    assert prev == 0
    return y


checks = {"quadratic complement collisions": 0, "quotient inputs": 0, "Patt permutation sizes": 0}
for k in range(1, 5):
    edges = list(combinations(range(k), 2))
    mon = [sum((((u >> i) & (u >> j)) & 1) << r for r, (i, j) in enumerate(edges)) for u in range(1 << k)]
    for q in range(1 << len(edges)):
        row = [0] * k
        for r, (i, j) in enumerate(edges):
            if (q >> r) & 1:
                row[i] ^= 1
                row[j] ^= 1
        for a in range(1 << k):
            if (a.bit_count() + q.bit_count()) % 2 != 1:
                continue
            T = [((a & u).bit_count() + (q & mon[u]).bit_count()) % 2 for u in range(1 << k)]
            if any(row):
                for n in (4, 8):
                    mask = (1 << n)-1
                    assert any(apply(T, x, n, k) == apply(T, x ^ mask, n, k) for x in range(1 << n))
                    checks["quadratic complement collisions"] += 1
            else:
                n = max(k, 3)
                mask = (1 << n)-1
                for x in range(1 << n):
                    y = apply(T, x, n, k)
                    z = integrate(d(x, n), n)
                    assert d(y, n) == d(apply(T, z, 2*n, k), 2*n) & mask
                    checks["quotient inputs"] += 1
patt = [((u >> 1) & 1) ^ ((1 ^ (u & 1)) & ((u >> 2) & 1) & (1 ^ (u >> 3))) for u in range(16)]
for n in range(4, 13):
    assert len({apply(patt, x, n, 4) for x in range(1 << n)}) == 1 << n
    checks["Patt permutation sizes"] += 1
for key, val in checks.items():
    print(key + ":", val)
