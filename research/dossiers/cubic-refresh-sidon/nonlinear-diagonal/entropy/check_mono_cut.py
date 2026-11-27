from fractions import Fraction
from itertools import combinations
from math import comb
from collections import Counter

cases=0
for n in range(4, 13, 2):
 for k in range(2, n//2+1):
  for t in range(2,k+1,2):
   outside=range(2*t,n)
   half=(n//2)-t
   fillers=[sum(1<<x for x in b) for b in combinations(outside,half)]
   chosen=[sum(1<<(2*i+((h>>i)&1)) for i in range(t)) for h in range(1<<t)]

   p=Fraction(comb(half,k-t),comb(n-2*t,k-t))
   hist=Counter()
   for S in combinations(range(n),k):
    sm=sum(1<<i for i in S)
    a=sum((-1)**h.bit_count()*((sm&~(base|side))==0 or (sm&(base|side))==0)
       for h,side in enumerate(chosen) for base in fillers)
    per_pair=[((sm>>(2*i))&3) for i in range(t)]
    e=2*p*(-1)**per_pair.count(2) if set(per_pair)<={1,2} else 0
    assert Fraction(a,len(fillers))==e
    hist[e]+=1;cases+=1
   assert sum(x*c for x,c in hist.items())==0
ineq=0
for k in range(2,100):
 for n in (16*k*k,16*k*k+2,32*k*k,1024*k*k):
  for t in range(2,k+1,2):
   eta=Fraction(8*k*k,n);x=Fraction(t*k,n-2*t)
   assert 1-Fraction(t*(k-t),n-t)>=Fraction(1,2)
   assert x<=eta/4 and x*x/eta<=Fraction(1,32)
   ineq+=1
print(cases,'exhaustive exact switch identities;',ineq,'rational bound controls')
