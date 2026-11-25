"""Independent finite sanity test; no role in the Lean proof."""
from collections import deque
from fractions import Fraction
from itertools import combinations, permutations

def check(G):
    n=len(G)
    ds=[]
    for v in range(n):
        dist={v:0}
        q=deque([v])
        while q:
            a=q.popleft()
            for b in G[a]:
                if b not in dist:
                    dist[b]=dist[a]+1
                    q.append(b)
        if len(dist)!=n:
            return None
        ds.append(dist)
    ecc=[max(row.values()) for row in ds]
    C=[v for v,e in enumerate(ecc) if e==min(ecc)]
    A=[ds[u][v] for u,v in permutations(C,2)]
    avg=Fraction(sum(A),len(A)) if A else Fraction(0)
    allv=set(range(n))
    gamma=next(k for k in range(2,n+1) if any(
        set().union(*(G[v] for v in S))==allv
        for S in combinations(range(n),k)))
    assert avg < gamma
    if min(ecc)==gamma:
        assert any(v in G[u] for u,v in combinations(C,2))
    return avg,gamma

count=0
for n in range(2,7):
    edges=list(combinations(range(n),2))
    for m in range(1<<len(edges)):
        if m.bit_count()<n-1: continue
        G=[set() for _ in range(n)]
        for i,(a,b) in enumerate(edges):
            if (m>>i)&1:
                G[a].add(b); G[b].add(a)
        count+=check(G) is not None
a,g=check([{1},{0}])
assert (a,g)==(1,2) and 1+a==g and 2+a>g
print(f'{count} labelled connected simple graphs of order 2..6: exact rational check passed.')
print('K2 negative control: raising the inner offset from 1 to 2 would require 3 <= 2.')
