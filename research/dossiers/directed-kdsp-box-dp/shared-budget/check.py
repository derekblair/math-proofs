"""Exact small checks of shared-vertex depot; no third-party libraries."""
from collections import Counter
from itertools import combinations, product
from random import Random

def shared(D):
    return {v for v,count in Counter(v for S,_,_,_ in D for v in S).items() if count>=2}

def paths(d):
    S,A,s,t=d
    def rec(u,used):
        if u==t:
            yield set(used)
        else:
            for v in A.get(u,()):
                yield from rec(v,used+(v,))
    return list(rec(s,(s,)))

def oracle(D,B,b):
    return sum(len(set.union(set(),*p))==sum(map(len,p)) and
               len(B & set.union(set(),*p))<=b
               for p in product(*map(paths,D)))

def colour(D,B,c):
    masks={0}
    for S,A,s,t in D:
        dp={v:set() for v in S}
        def insert(v,x):
            if v not in B:
                dp[v].add(x)
            else:
                re=1<<c[v]
                if not re&x:dp[v].add(re|x)
        for x in masks:insert(s,x)
        for u in S:
            if u==t:continue
            for v in A.get(u,()):
                for x in dp[u]:insert(v,x)
        masks=dp[t]
    return bool(masks)

def full_cover(D,B,b):
    S0=tuple(sorted(B))
    # Mark each selected shared visit with a formal x. Marking the unused dummy
    # set also consumes one degree per vertex. Degree r + full support => disjoint.
    # A second degree quota would be equivalent; track (total, graph visits).
    r=len(B); total=0
    for w in range(1<<r):
        S={v for i,v in enumerate(S0) if w>>i&1}
        start={(0,0):1}
        for T,A,s,t in D:
            dp={v:Counter() for v in T}
            def transfer(v,src):
                if v in B and v not in S:return
                inc=int(v in B)
                for (a,h),c in src.items():
                    if a+inc<=r and h+inc<=b:dp[v][a+inc,h+inc]+=c
            transfer(s,start)
            for u in T:
                if u==t:continue
                for v in A.get(u,()):transfer(v,dp[u])
            start=dp[t]
        from math import comb
        term=sum(c*comb(len(S),r-a) for (a,h),c in start.items() if r-a<=len(S))
        total+=(-1 if (r-len(S))%2 else 1)*term
    return total

def fixture(rng,n,k):
    D=[]
    for _ in range(k):
        order=rng.sample(range(n),rng.randint(1,n))
        edges={u:[v for v in order[i+1:] if rng.random()<0.45] for i,u in enumerate(order)}
        D.append((order,edges,order[0],order[-1]))
    return D

if __name__=='__main__':
    rng=Random(412)
    graphs=checks=0
    for n in range(1,8):
        for _ in range(60):
            D=fixture(rng,n,rng.randint(1,4)); B=shared(D); graphs+=1
            for b in range(len(B)+1):
                exact=oracle(D,B,b)
                assert full_cover(D,B,b)==exact,(D,B,b)
                # Complete color-family for tiny examples; no randomness in completeness.
                ans=False
                if b==0:
                    ans=colour(D,B,{v:0 for v in B}) if not B else D and all(any(not B&p for p in paths(d)) for d in D)
                else:
                    ans=any(colour(D,B,{**dict.fromkeys(B,0),**dict(zip(Q,range(b)))})
                            for Q in combinations(sorted(B),b))
                assert bool(exact)==bool(ans),(D,B,b,exact,ans)
                checks+=1
    print(graphs, 'graphs;', checks,'quota/inclusion-exclusion/color comparisons')
