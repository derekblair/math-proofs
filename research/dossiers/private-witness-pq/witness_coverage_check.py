#!/usr/bin/env python3
from itertools import combinations
from math import comb
from random import Random

def hit_number(supports,n):
    for t in range(n+1):
        for parts in combinations(range(n),t):
            b=sum(1<<j for j in parts)
            if all(b&s for s in supports):
                return t
    raise AssertionError

def construction(w,s,r):
    n=0
    supports=[]
    def block(a):
        nonlocal n
        out=((1<<a)-1)<<n
        n+=a
        return out
    if r==1:
        for _ in range(s):
            a=block(1)
            supports.extend((a,a))
        singles=w-2*s
    else:
        for _ in range(s):
            a,b,c=[block(i) for i in (r//2,(r+1)//2,(r+1)//2)]
            supports.extend((a|b,a|c,b|c))
        singles=w-3*s
    for _ in range(singles):
        supports.append(block(r))
    return supports,n

rng=Random(2332)
for t in range(4000):
    n=rng.randrange(1,11); r=rng.randrange(1,n+1); w=rng.randrange(1,12)
    h=[sum(1<<i for i in rng.sample(range(n),r)) for _ in range(w)]
    tau=hit_number(h,n)
    assert n >= w*r -(w-tau)*(3*r//2)

exact=0
for r in range(1,8):
    for w in range(1,12):
        for s in range(w//3+1):
            h,n=construction(w,s,r)
            assert n==w*r-s*(3*r//2)
            assert len(h)==w and all(x.bit_count()>=r for x in h)
            if n<=13:
                assert hit_number(h,n)==w-s
                exact+=1

# Count a support's covered size-c exposure sets and verify uniform balance.
counts=0
for n in range(1,10):
    for r in range(1,n+1):
        for c in range(n-r+1):
            R=list(map(set,combinations(range(n),r)))
            C=list(map(set,combinations(range(n),c)))
            assert all(sum(a.isdisjoint(b) for b in C)==comb(n-r,c) for a in R)
            assert all(sum(a.isdisjoint(b) for a in R)==comb(n-c,r) for b in C)
            assert comb(n-r,c)*comb(n,r)==comb(n,c)*comb(n-c,r)
            counts+=1
print(f'4000 random transversal checks, {exact} exact constructions, {counts} balanced-incidence controls')
