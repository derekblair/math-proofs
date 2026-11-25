"""Independent randomized checks using actual positions, not rank scores."""
from random import Random


def test(p, j):
    width = len(p)
    step = width-2
    n = j*step+2
    inv = sorted(range(width), key=p.__getitem__)
    reach = [1 << i for i in range(n)]
    for t in range(j):
        for low, high in zip(inv, inv[1:]):
            reach[t*step+low] |= 1 << (t*step+high)
    for mid in range(n):
        for x in range(n):
            if reach[x] >> mid & 1:
                reach[x] |= reach[mid]
    z = width-1
    left = [x for x in range(n) if x != z and reach[x] >> z & 1]
    right = [x for x in range(n) if x != z and reach[z] >> x & 1]
    assert len(set(left+right)) == n-1
    assert set(left).isdisjoint(right)
    def has_incomparable(xs):
        return any(not ((reach[a]>>b)&1 or (reach[b]>>a)&1)
                   for a in xs for b in xs)
    assert has_incomparable(left) and has_incomparable(right)


rng = Random(20261125)
for _ in range(240):
    K = rng.randint(7, 23)
    a = rng.randrange(2, K-3)
    b = rng.randrange(a+1, K-2)
    c = rng.randrange(b+2, K)
    private = [u for u in range(K) if u not in {0,a,b,c}]
    rng.shuffle(private)
    test([0,a]+private+[b,c],rng.randrange(3,12))
print("240 independent physical-window controls passed.")
