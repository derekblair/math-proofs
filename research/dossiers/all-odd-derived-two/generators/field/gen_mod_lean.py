from cover import *
from json import loads
from pathlib import Path
from functools import lru_cache
from sympy import ZZ
CS=loads(Path('slope-integer.json').read_text());MS=loads(Path('slope-modular.json').read_text())
LS={(p,tuple(f)):Z for p,f,Z in loads(Path('slope-leaves.json').read_text())}
def op(f):return Poly(sum(v*t**i for i,v in enumerate(f)if v),t,domain=ZZ)
def fmt(P):return list(map(int,reversed(P.all_coeffs()))) if not P.is_zero else []
def li(x):return '['+','.join(map(str,x))+']'
def ar(x):return '#'+li(x)
def pol(P):return li(f'({i},0,{c})' for i,c in reversed(list(enumerate(P))) if c)
def ide(A,B,C,D,R):return '⟨'+','.join([pol(A),pol(B),pol(C),pol(D),pol(R)])+'⟩'
def coeff(p):return fmt(p)
def nt(q):
 rs=[]
 for p,a in sorted(q.items()):rs += [p]*a
 return rs
@lru_cache(None)
def leaf(p,F):
 Z=LS[p,F]
 if len(Z)==1:return f'.linear {p} '+str(Z[0]),[-Z[0],1]
 o,d,Q,E,G,H,I=Z
 x2=x3=0
 while o%2==0:x2+=1;o//=2

 assert o==d
 e=d*2**x2*3**x3
 return f'.reject {pol(F)} ⟨{e},{d},{x2},{x3},{ide(Q,[],[],E,[-1]+[0]*(e-1)+[1])},{ide(G,H,[],I,[1])}⟩',F

for subset in range(10):
 lo=subset*8;rr=[]
 for bc,ms in zip(CS[lo:lo+8],MS[lo:lo+8],strict=True):
  u,v,f,q,ds=bc;F=op(f)
  prim=[]
  for rid,(d,g,n,*_) in enumerate(ds):
   D=op(g);B=Poly(t**d-1,t,domain=ZZ)
   fs=factorint(n);pp=fs.pop(2,0);fs.pop(-1,None)
   rows=[]
   for p in nt(fs):
    entry=next(A for A in ms[str(p)] if A[0]==rid)
    _,e,X,Y,Z,ff=entry
    lf=Poly(1,t,domain=ZZ);ll=[]
    for l,o in ff:
     s,l=leaf(p,tuple(l));ll.append(s);lf*=op(l)
    h=(lf-op(X)*F-op(Y)*D-op(Z)*B).exquo_ground(p)
    rows.append(f'⟨{p},{ide(X,Y,Z,coeff(h),coeff(lf))},{li(ll)}⟩')
   prim.append(f'⟨{pp},{li(rows)}⟩')
  rr.append(ar(prim))
 N=len(rr)
 Path(f'RibbonAllOddModData{subset}.lean').write_text(f'''import RibbonAllOddModular
import RibbonAllOddSlopeData{subset}
namespace RibbonAllOddField
open RibbonStationaryField (branch)
set_option maxHeartbeats 0
set_option maxRecDepth 40000
def modData{subset} : Array (Array PrimeCert) := #[\n'''+',\n'.join(rr)+f''']
def mp{subset} (k : Fin {N}) (r : Nat) := (modData{subset}[k.val]!)[r]!
def modSpec{subset} (k : Fin {N}) : Prop :=
  ∀ r : Fin data{subset}[k.val]!.rows.size,
    primeValid (branch ({lo}+k.val)) data{subset}[k.val]!.rows[r] (mp{subset} k r.val)
instance (k : Fin {N}) : Decidable (modSpec{subset} k) := by unfold modSpec{subset}; infer_instance
theorem modProof{subset} (k : Fin {N}) : modSpec{subset} k := by
  fin_cases k <;> decide +kernel
end RibbonAllOddField
''')
