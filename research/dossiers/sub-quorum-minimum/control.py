from itertools import combinations
from math import comb

def parts(a, k, n):
    if len(a) == n:
        yield a
    else:
        for x in range(k + 2):
            yield from parts(a+(x,), max(k,x), n)

counts = graphs = 0
for n in range(2,6):
    edges = list(combinations(range(n),2))
    qs = list(parts((),0,n))
    values = []
    for bits in range(1<<len(edges)):
        adj = [set() for _ in range(n)]
        for i,(x,y) in enumerate(edges):
            if bits>>i&1:
                adj[x].add(y)
                adj[y].add(x)
        def valid(f):
            for x,c in enumerate(f):
                if c and 2*(1+sum(f[y]==c for y in adj[x])) < 1+sum(bool(f[y]) for y in adj[x]):
                    return False
            return True
        best = 0
        for f in qs:
            if not valid(f):
                continue
            counts += 1
            m = max(f)
            best = max(best, m)
            S = [x for x,c in enumerate(f) if c]
            e = sum(y in adj[x] for x,y in combinations(S,2))
            if S and 8*e >= len(S)*(len(S)-1):
                M = max(f.count(i) for i in range(1,m+1))
                assert 8*M >= len(S)+3
            for i in range(1,m+1):
                assert valid(tuple(0 if c==i else c for c in f))
        values.append(best)
        graphs += 1
    a = min(x+values[-i-1] for i,x in enumerate(values))
    assert n < 2**a
    print(n,a)
for r in range(1,61):
    assert sum(comb(8*r,i) for i in range(2*r+1)) <= 2**(7*r)
print(f'{graphs} graphs, {counts} valid partial colorings, and 60 exact bit-tail boundaries: PASS')
