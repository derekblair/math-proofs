"""Independent enumeration on actual physical windows; not used in Lean."""
from functools import cache
from math import comb


def pattern(m, K):
    z, h = m - 2, K - 2*m
    F = 2*z + h
    return [*range(z), F+1, F+3, *range(z, z+h),
            *range(z+h, F), F, F+2]


def exact_count(p, m, j):
    K = len(p)
    d = K - m
    n = K + (j-1)*d
    inverse = sorted(range(K), key=p.__getitem__)
    pred = [0] * n
    for k in range(j):
        for x, y in zip(inverse, inverse[1:]):
            pred[k*d+y] |= 1 << (k*d+x)

    @cache
    def count(taken):
        if taken == (1 << n)-1:
            return 1
        return sum(count(taken | (1 << u)) for u in range(n)
                   if not (taken >> u)&1 and pred[u] & ~taken == 0)
    return count(0)


n = 0
for m in range(3, 10):
    for K in range(2*m, 2*m+6):
        p = pattern(m, K)
        assert sorted(p) == list(range(K))
        for j in range(1, 8):
            actual = exact_count(p, m, j)
            assert actual == comb(2*j, j)//(j+1), (m, K, j, p, actual)
            n += 1
print("independent physical-window counts:", n)
print("m=3, K=7 pattern:", ''.join(str(x+1) for x in pattern(3,7)))
