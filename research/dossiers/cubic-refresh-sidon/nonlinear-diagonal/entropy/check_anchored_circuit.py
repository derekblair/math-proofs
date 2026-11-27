from itertools import combinations
from fractions import Fraction
from math import comb,log2
from collections import Counter

P={3:11,4:19,5:37}
def mul(a,b,r):
    out=0
    while b:
        if b&1:out^=a
        a<<=1
        if a&(1<<r):a^=P[r]
        b>>=1
    return out

histograms=0
for n,r in [(10,4),(12,4),(16,5)]:
    m=n//2; q=1<<r
    if q<=n:continue
    T=list(combinations(range(1,n),r))
    Z=Fraction(comb(m-1,r),len(T))
    alpha=(Fraction(1,q)-Z)/(1-Z)
    assert 0<alpha<1
    # Cut symmetry: test all balanced sets for n≤12; indexed witnesses at n=16.
    for j,A0 in enumerate(combinations(range(n),m)):
        if n==16 and j not in (0,123,270,902,1056,6430,12001,12869):continue
        A=set(A0)
        hist=Counter()
        for t in T:
            val=(q-1 if 0 in A else 0)
            for i,a in enumerate(t):
                if a in A:val^=1<<i
            hist[val]+=1
        assert Fraction(hist[0],len(T))==Z
        normal=Counter()
        for val,ct in hist.items():
            for s in range(1,q):
                normal[mul(s,val,r)]+=ct
        for h in range(q):
            assert (1-alpha)*Fraction(normal[h],len(T)*(q-1)) + (alpha if h==0 else 0)==Fraction(1,q)
        histograms+=1
    a=float(alpha)
    H=-a*log2(a)-(1-a)*log2(1-a)+(1-a)*log2(len(T)*(q-1))
    print(n,r,'alpha=',alpha,'bits=',round(H,7),'ordered=',round(r*log2(n),7))
print(histograms,'exact scaled and mixed field histograms')
