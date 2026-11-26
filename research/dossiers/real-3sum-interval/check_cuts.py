"""Test exact block cuts with duplicate original inputs; no asymptotic solver."""
from itertools import product
from bisect import bisect_left
from random import Random

def verify(a,b,C,d):
    a=sorted((v,i+1) for i,v in enumerate(a))
    M=len(a)+1
    b=sorted((v,(j+1)*M) for j,v in enumerate(b))
    high=M*(len(b)+1)
    la=[a[k:k+d] for k in range(0,len(a),d)]
    lb=[b[k:k+d] for k in range(0,len(b),d)]
    plus=lambda x,y:(x[0]+y[0],x[1]+y[1])
    all_sums=[x[0]+y[0] for x,y in product(a,b)]
    def prefix(threshold):
        full=0; count=0; seen=set()
        for i,u in enumerate(la):
          for j,v in enumerate(lb):
            lo=plus(u[0],v[0]); hi=plus(u[-1],v[-1])
            if hi<threshold: full+=len(u)*len(v)
            elif lo<threshold<=hi:
                assert i-j not in seen
                seen.add(i-j)
                count+=bisect_left(sorted(plus(x,y) for x,y in product(u,v)),threshold)
        assert len(seen)<=len(la)+len(lb)-1
        return full+count
    for c in C:
        v=prefix((c,high))-prefix((c,0))
        assert v==all_sums.count(c)
    return len(C)

rng=Random(5223);num=0
for _ in range(500):
    n,m,d=[rng.randrange(1,19) for i in range(3)]
    a,b=[[rng.randrange(-9,10) for i in range(p)] for p in [n,m]]
    num+=verify(a,b,list(range(-20,21)),d)
print(f'{num} exact per-target tied counts and staircase bounds passed')
