from cover_surface import *
from sympy import div, ZZ, QQ
from itertools import chain
from math import lcm
from pathlib import Path
def partition(raw):
 if not raw:return (0,0,1,0,Poly(0,b,domain=ZZ))
 sx=-min(i for i,j in raw);sy=-min(j for i,j in raw)
 h=max(i+sx for i,j in raw);cc=2**h
 scaled=expand(cc*sum(v*a**(i+sx)*b**(j+sy) for (i,j),v in raw.items()))
 A,re=div(scaled,2*a+1,a)
 return (sx,sy,cc,Poly(A,a,b,domain=ZZ),Poly(re,b,domain=ZZ))
def R0(i,j): 
 C=Counter({(0,0):-1});C[i,j]+=1
 return {k:v for k,v in C.items()if v}
def li(xs):return '['+','.join(map(str,xs))+']'
def ar(xs):return '#'+li(xs)
def pol(P):
 if P==0:return '[]'
 if P.gens==(b,):return li(f'(0,{j},{c})'for (j,),c in P.terms()if c)
 return li(f'({i},{j},{c})'for (i,j),c in P.terms()if c)
def showcase(A):
 i,j,c,q,p=A
 return f'⟨({i},{j},{c}),{pol(q)},{pol(p)}⟩'
def idstr(A,B,C,D,E):return '⟨'+','.join(pol(q)for q in [A,B,C,D,E])+'⟩'
def balance(f,g,G,p=0):
 # A*f+B*g = target, over QQ or modulo p, returning an integral identity.
 ff=f.set_modulus(p) if p else f.to_field();gg=g.set_modulus(p) if p else g.to_field()
 HH=G.set_modulus(p) if p else G.to_field()
 zero=Poly(0,b,domain=ZZ)
 if ff.is_zero and gg.is_zero:
  assert G.is_zero
  return 1,idstr(0,0,0,0,0)
 if gg.is_zero:
  A,B,R=Poly(1,b,domain=ff.domain),ff*0,ff
 elif ff.is_zero:
  A,B,R=gg*0,Poly(1,b,domain=gg.domain),gg
 else:A,B,R=ff.gcdex(gg)
 Q=HH.exquo(R)
 A*=Q;B*=Q
 if not p:
  n=lcm(*(int(c.q) for c in chain(A.all_coeffs(),B.all_coeffs())))
  ai=(n*A).to_ring();bi=(n*B).to_ring();rr=n*G
  assert ai*f+bi*g==rr
  return n,idstr(ai,bi,0,0,rr)
 ai=Poly(A.as_expr(),b,domain=ZZ);bi=Poly(B.as_expr(),b,domain=ZZ)
 debt=(G-ai*f-bi*g).exquo_ground(p)
 return 1,idstr(ai,bi,0,debt,G)
def aggregate(L,p=0):
 if not p:
  a=Poly(1,b,domain=QQ)
  for f,g in L:a=a.lcm(f.to_field().gcd(g.to_field()))
  return a.clear_denoms(convert=True)[1].primitive()[1]
 a=Poly(1,b,modulus=p)
 for f,g in L:a=a.lcm(f.set_modulus(p).gcd(g.set_modulus(p)))
 return Poly(a.as_expr(),b,domain=ZZ)

ids=[]
for q,p in ((0,19),(0,67),(4,19),(4,67),(6,19),(6,67)):
 tab={(i,j):(partition(H),partition(R0(x,y))) for i,j,x,y,H in pairs(W[q])}
 E=list(dict.fromkeys(tab.values()))
 Z=[(F[-1],G[-1])for F,G in E]
 normal=aggregate(Z,p)
 I=[balance(f,g,normal,p)[1] for f,g in Z]
 ids.append((p,q,normal,I))
records=[]
for p in (19,67):
 L=[r[2]for r in ids if r[0]==p]
 x,y,z=[v.set_modulus(p) for v in L]
 A,B,D=x.gcdex(y);C,E,F=D.gcdex(z)
 assert F==Poly(b+1,b,modulus=p)
 coeffs=[(A*C).set_domain(ZZ),(B*C).set_domain(ZZ),E.set_domain(ZZ)]
 G=Poly(b+1,b,domain=ZZ)
 debt=(G-sum((a*f for a,f in zip(coeffs,L)),Poly(0,b,domain=ZZ))).exquo_ground(p)
 J=idstr(*coeffs,debt,G)
 records.append((p,J))

Path('RibbonAllOddSurfaceData.lean').write_text("""import RibbonStationarySurface
namespace RibbonAllOddField
open RibbonStationaryField
set_option maxHeartbeats 0
set_option maxRecDepth 30000
def surfaceNewValid (p : Nat) (S : SurfaceSpec) (cost : Array Id) (out : Poly) : Prop :=
  ∀ r : Fin S.rows.size, let x := S.rows[r];
    cost[r.val]!.rhs=out ∧ cost[r.val]!.valid x.trans.out x.multiplier.out [] p
instance (p : Nat) (S : SurfaceSpec) (cost : Array Id) (out : Poly) :
    Decidable (surfaceNewValid p S cost out) := by unfold surfaceNewValid; infer_instance
""" + ''.join(f"""
def data{p}_{s} : Array Id := {ar(I)}
def norm{p}_{s} : Poly := {pol(A)}
theorem valid{p}_{s} : surfaceNewValid {p} surf{s} data{p}_{s} norm{p}_{s} := by decide +kernel
""" for p,q,A,I in ids for s in [(0,4,6).index(q)])+''.join(f"""
def join{p} : Id := {J}
theorem join{p}Valid : join{p}.rhs=surfGcd ∧ join{p}.valid norm{p}_0 norm{p}_1 norm{p}_2 {p} :=
  by decide +kernel
""" for p,J in records) + "end RibbonAllOddField\n")
