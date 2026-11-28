"""Independent small enumerations and the large rational DP certificate."""
from itertools import product
from fractions import Fraction as Fq
from math import comb
from waterfill import level,demand,best_at,solve

def p(n,r,e):
    return Fq(comb(n-e,r),comb(n,r))

small=0
for r in range(1,4):
    for L in range(1,4):
        for layout in product(range(r,r+4),repeat=L):
            D=sum(n-r+1 for n in layout)
            for c in range(D+1):
                t=level(layout,c,r)
                if c==0 or c==D:
                    assert t==Fq(c==0)
                    continue
                es=[demand(n,r,t) for n in layout]
                e0=[e.numerator//e.denominator for e in es]
                ds=[p(n,r,k)-p(n,r,k+1) for n,k in zip(layout,e0)]
                assert sum(es)==c and all(d>0 for d in ds)
                weights=[1/d for d in ds]
                weights=[w/sum(weights) for w in weights]
                brute=min(sum(q*p(n,r,e) for n,q,e in zip(layout,weights,E))
                          for E in product(*(range(n+1) for n in layout)) if sum(E)==c)
                assert brute==t
                small+=1

def layouts(n,lo,cur=()):
    if cur:yield cur
    for i in range(lo,n+1):
        yield from layouts(n-i,i,cur+(i,))

brute=0
for f in (1,2):
    for N in range(5,12):
        A=list(layouts(N,f+1))
        for c in range(1,5):
            for cap in range(c+1,8):
                U=[L for L in A if c<sum(L)-f*len(L)<=cap]
                if not U:continue
                low=max(level(L,c,f+1) for L in U)
                t,layout,_=solve(c,f,N,cap)
                assert t==low and layout in U and sum(demand(n,f+1,t) for n in layout)==c
                brute+=1

L=Fq(43,21220); layout=(16,18,18,18,18,21,21)
assert level(layout,63,7)==L and best_at(L,63,6,130,88)[0]==63
print(small,'exact strategy allocation enumerations;',brute,'brute-force layout comparisons')
print('cap-88 certificate',L,layout,'max demand 63')
