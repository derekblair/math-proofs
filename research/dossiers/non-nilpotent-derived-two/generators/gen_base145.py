from cover import *
from sympy import div
from pathlib import Path
from math import gcd
base=145; bi=8
branch=t_branches(base); bm={j:i for i,j in enumerate(branch)}
r,w,M=W[base]; A=row(r,w)
def li(xs):return '['+','.join(map(str,xs))+']'
def ar(xs):return '#'+li(xs)
def mo(i,j,c):return f'({i},{j},{c})'
def uni(f):
 f=Poly(f,t)
 return li(mo(i,0,c)for (i,),c in f.terms()if c)
def bz(x,y):
 return next((p,q) for p in range(-5,6) for q in range(-5,6) if p*y-q*x==1)
SIM=['a - 1','a + 1','b + 1','2*a + 1']
B=[]
for i in range(64):
  L=[]
  for j in range(64):
   if i>=j:L.append('.side');continue
   l,x,y,p=A[i];m,u,v,q=A[j];x-=u;y-=v
   if l!=m:L.append('.side');continue
   if (i,j) in M:L.append('.mate');continue
   H={k:p[k]-q[k] for k in p.keys()|q.keys() if p[k]!=q[k]}
   d=gcd(x,y)
   if not y and x:L.append(f'.axis ({x})');continue
   if not d:
    a0=min(x for x,y in H);b0=min(y for x,y in H);c,fs=factor_list(bip(H),a,b)
    assert abs(c) in (1,2)
    L.append(f'.same {mo(a0,b0,c)} '+li(SIM.index(str(f)) for f,e in fs for _ in range(e)))
    continue
   x//=d;y//=d
   if y<0:x,y,d=-x,-y,-d
   P=Counter()
   for (u,v),k in H.items():P[u*y-v*x]+=k
   t0=min(i for i,k in P.items() if k)
   P=sum(k*t**(i-t0)for i,k in P.items() if k)
   p,q=bz(x,y);c,fs=factor_list(P,t)
   assert abs(c) in (1,2)
   F=[]
   for f,e in fs:
    if str(f) in ignoret:
     E=next(E for E in (1,2,3,4,6)if div(t**E-1,f,t)[1]==0)
     Q=div(t**E-1,f,t)[0]
     F.extend(f'.drop {E} {uni(f)} {uni(Q)}' for _ in range(e))
    else:F.extend(f'.bad {bm[x,y,Poly(f,t)]}' for _ in range(e))
   L.append(f'.slope ({x}) ({y}) ({d}) ({p}) ({q}) {mo(t0,0,c)} '+li(F))
  B.append(ar(L))
Path('RibbonStationaryBaseData.lean').write_text('''import RibbonStationaryBaseCore
namespace RibbonStationaryField
open RibbonStationaryWord
def base : Count := '''+str(bi)+'''
def branches : Array Branch := #[\n  '''+',\n  '.join(f'⟨{u},{v},{uni(f)}⟩' for u,v,f in branch)+''']
def branch (r : Nat) : Branch := branches[r]!
def cases145 : Array (Array PairCase) := #[\n'''+',\n'.join(B)+''']
def chooseCase (i j : Fin 64) := (cases145[i.val]!)[j.val]!
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem base_valid : ∀ (i j : Fin 64), i.val<j.val → valid branch base i j (chooseCase i j) := by decide +kernel
end RibbonStationaryField
#print axioms RibbonStationaryField.base_valid
''')
