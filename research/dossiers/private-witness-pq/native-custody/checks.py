"""Finite arithmetic and abstract model checks only; no crypto implementations."""
from itertools import combinations,product
from collections import Counter
from fractions import Fraction
from math import ceil,log2

def ev(f,x,p):
    v=0
    for a in reversed(f):v=(x*v+a)%p
    return v

checks=0
for p,n,t,c in [(5,4,3,1),(7,6,4,2),(7,5,3,2),(5,4,2,0)]:
    S=tuple(range(1,n+1))
    for R in combinations(S,t):
        # All coefficient vectors yield different interpolating views.
        assert len({tuple(ev(f,x,p) for x in R) for f in product(range(p),repeat=t)})==p**t
        checks+=1
    for e in range(c+1):
        for R in combinations(S,e):
            for seed in product(range(p),repeat=t-c):
                H=Counter(tuple(ev(mask+seed,x,p) for x in R)
                          for mask in product(range(p),repeat=c))
                assert len(H)==p**e and set(H.values())=={p**(c-e)}
                checks+=1

sizes=0
for H in range(1,12):
    for t in range(1,7):
        for c in range(t):
            L=t-c; bound=H+c*ceil(H/L)
            feasible=[]
            for W in combinations(range(H+t),t):
                W=tuple(b-i for i,b in enumerate(W))
                if sum(W[:L])>=H: feasible.append(sum(W))
            assert min(feasible)==bound
            sizes+=1

n=130;c=63;t=85
w=lambda H,k:max(ceil(H/(k-c)),ceil(log2(n+1)))
assert w(512,t)==24 and w(256,t)==12 and w(512,64)==512
assert t*w(512,t)//8==255 and 64*w(512,64)//8==4096
assert Fraction(t*(w(512,t)+w(256,t)),8)==Fraction(765,2)
assert (512+63*24)//8==253
assert 130*(1088+32)==145600 and 130*(1088+8978+64)==1316900
assert 85*32==2720 and 85*64==5440
# Independent abstract contexts: one-time input labels and visible pads
# in ordinary contexts constrain no challenge-context function value.
for off in product((0,1),repeat=3):
    observed={tuple(table[1:]) for table in [(0,*off),(1,*off)]}
    assert len(observed)==1
    out0=Counter((table[0]^0,*table[1:]) for table in [(0,*off),(1,*off)])
    out1=Counter((table[0]^1,*table[1:]) for table in [(0,*off),(1,*off)])
    assert out0==out1
print(checks,'finite ramp checks;',sizes,'integer width minima; fixed cost and symbolic snapshot checks green')
