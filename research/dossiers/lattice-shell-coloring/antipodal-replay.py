from fractions import Fraction as Q
from math import comb

def binom_poly(a, b, n):
    return [comb(n, k) * a**(n-k) * b**k for k in range(n+1)]

def mul(a, b):
    c = [Q(0)] * (len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j] += x*y
    return c

def integral(a, lo, hi):
    return sum(x*(hi**(i+1)-lo**(i+1))/(i+1) for i,x in enumerate(a))

cases=0
for d in range(3,16,2):
    weight=binom_poly(Q(1),Q(-1),(d-3)//2)
    weight=[c for i,x in enumerate(weight) for c in [x,Q(0)]][:-1]
    for A in [Q(1), Q(5,4), Q(3,2), Q(2), Q(5)]:
        for b in [Q(0), Q(1,10), Q(3,4), Q(1)]:
            fn=mul(weight,binom_poly(A,b,d))
            positive=integral(fn,Q(0),Q(1))
            total=integral(fn,Q(-1),Q(1))
            overlap=2*integral(fn,Q(-1),Q(0))
            assert positive==total-overlap/2
            assert 0<=overlap<=A**d*integral(weight,Q(-1),Q(1))
            cases+=1
print('passed',cases,'exact odd-dimensional antipodal integral identities and bounds')
