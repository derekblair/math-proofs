"""Synthetic combinatorics only. No encryption or endpoint code."""
from itertools import combinations, product
from fractions import Fraction
from math import comb

def masks(n,k):
    return [sum(1<<i for i in S) for S in combinations(range(n),k)]
def pad(E,c,n):
    for i in range(n):
        if E.bit_count()>=c:break
        E|=1<<i
    return E

normalization=0
for n in range(2,9):
    for c in range(n):
        for r in range(1,n-c+1):
            U=masks(n,r); p=Fraction(comb(n-c,r),len(U))
            # Classical adaptive transcripts fixture: a synthetic classical
            # reply at each step can change which domain is exposed next.
            # The candidate support never affects legitimate real replies.
            real=0;restricted=0
            for coins in product(range(2),repeat=5):
                E=0; state=coins[0]
                requested=[]
                for t,j in enumerate(coins[1:]):
                    endpoint=(i0:=((state+1)*7+3*j+2*t)%n)
                    if E.bit_count()<c:
                        E|=1<<endpoint
                        requested.append(1<<endpoint)
                    state=3*state+endpoint+j
                accept=(state%7<4)
                if not accept:continue
                real+=1
                D=pad(E,c,n)
                for S in U:
                    full_event=(D&S)==0
                    early_stop=any(x&S for x in requested)
                    assert full_event==((not early_stop) and (D&S)==0)
                    restricted+=full_event
                normalization+=1
            assert Fraction(restricted,len(U))==p*real

arithmetic=0
for n in range(1,65):
    for c in range(n):
        for r in range(1,n-c+1):
            b=n-c
            estimates=[Fraction(d+1,comb(b+d,r)) for d in range(c+1)]
            star=c if r==1 else max(0,min(c,-(-(b+1-2*r)//(r-1))))
            assert estimates[star]==max(estimates)
            arithmetic+=1

n,c,r=130,63,7
p=Fraction(comb(n-c,r),comb(n,r))
low=max(Fraction((d+1)*comb(n,r),comb(n-c+d,r)) for d in range(c+1))
S=1
for d in range(1,c+1):
    den=n-c+d-r
    S=((n-c+d)*S+den-1)//den
assert -(-low.numerator//low.denominator)==484 and S==744
print(normalization,'adaptive transcript thinning controls;',arithmetic,'discrete maximizer controls')
print('reciprocal p:',float(1/p),'two-family factor:',float(2*2*r/p))
