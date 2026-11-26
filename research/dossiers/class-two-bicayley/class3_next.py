#!/usr/bin/env python3
from itertools import product
deg=3
basis=('',)+tuple(''.join(s) for n in range(1,deg+1) for s in product('ab',repeat=n))
unit=(1,)+(0,)*(len(basis)-1)
terms={ (g,s): tuple(tuple((basis.index(w[:-k]),s**k if s==-1 else 1) for k in range(1,len(w)+1) if w.endswith(g*k) and (s==-1 or k==1)) for w in basis) for g in 'ab' for s in [-1,1] }
def move(u,g,s):
 return tuple(u[i]+sum(u[j]*c for j,c in rs) for i,rs in enumerate(terms[g,s]))
def find(length):
 # All alternating signed rim edges, one intervening spoke after each edge.
 result=[]
 def visit(w, states):
  h=states[-1]
  g='ab'[len(w)%2]
  for s in (1,-1):
   nxt=move(h,g,s)
   if len(w)+1==length:
    if nxt==unit: result.append(w+str(int(s==1)))
   elif nxt not in states:
    visit(w+str(int(s==1)), states+(nxt,))
 visit('',(unit,))
 return result
for n in (4,8,16):
 out=find(n)
 print(n, len(out), out[:10])
def trace_hee(word,p):
 x,y,z=0,0,0
 seen=set()
 for i,pin in enumerate(word):
  if (x,y,z) in seen: return False
  seen.add((x,y,z))
  s=1 if pin=='1' else -1
  if i%2:
   y=(y+s)%p
   z=(z+x*s)%p
  else:
   x=(x+s)%p
 return (x,y,z)==(0,0,0)
for ks in [(3,), (5,), (3,5,7,11)]:
 ok=[w for w in out if all(trace_hee(w,p) for p in ks)]
 print("class-two separation controls",ks,len(ok),ok[:4])
def integer_sep(word, maxdegree):
 take=[i for i,w in enumerate(basis) if len(w)<=maxdegree]
 seen=set()
 u=unit
 for i,pin in enumerate(word):
  v=tuple(u[j] for j in take)
  if v in seen: return False
  seen.add(v)
  u=move(u,'ab'[i%2],1 if pin=='1' else -1)
 return u==unit
assert all(integer_sep(w,3) for w in out)
print("class-two integer separation",sum(integer_sep(w,2) for w in out))
