from random import Random
from fractions import Fraction as F
from math import lcm
from itertools import product

def det(a,b,c): return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def inter(a,b,c,d):
    x,y=b[0]-a[0],b[1]-a[1]
    div=x*(d[1]-c[1])-y*(d[0]-c[0])
    if not div: return None
    t=F((c[0]-a[0])*(d[1]-c[1])-(c[1]-a[1])*(d[0]-c[0]),div)
    return (a[0]+t*x,a[1]+t*y)
def norm(seq):
    denom=lcm(*(F(x).denominator for p in seq for x in p))
    return [tuple(int(denom*z) for z in p) for p in seq]
rng=Random(2)
want={(0,0,0),(1,1,1),(2,2,2),(1,2,0),(2,0,1)}
best=None
for z in range(20000):
 a=[tuple(rng.randint(-3,3) for _ in range(2)) for _ in range(3)]
 b=[tuple(rng.randint(-3,3) for _ in range(2)) for _ in range(3)]
 if len(set(a+b))<6:continue
 u=inter(a[0],b[0],a[1],b[2]);v=inter(a[1],b[1],a[2],b[0])
 if u is None or v is None:continue
 c=[u,v,tuple(x+y for x,y in zip(a[2],b[2]))]
 c[-1]=tuple(F(x,2) for x in c[-1])
 if len(set(a+b+c))!=9:continue
 actual={(i,j,k) for i,j,k in product(range(3),repeat=3) if det(a[i],b[j],c[k])==0}
 if want!=actual:continue
 A=norm(a+b+c)
 best=min(best or (10**9,[]),(max(abs(t) for p in A for t in p),A))
print(best)
