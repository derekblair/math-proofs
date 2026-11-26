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
data=[]; allNs=[];wordP=[]
for w,lean in ((0,0),(4,3),(6,5)):
 rawCases=pairs(W[w]); tab={(i,j):(partition(H),partition(R0(x,y))) for i,j,x,y,H in rawCases}
 E=list(dict.fromkeys(tab.values()))
 shapes=[v for v in E]
 pairsOnly=[(F[-1],G[-1])for F,G in shapes]
 A=aggregate(pairsOnly)
 B=aggregate(pairsOnly,11) if w==0 else Poly(0,b,domain=ZZ)
 C=aggregate(pairsOnly,43) if w in (0,4) else Poly(0,b,domain=ZZ)
 print(w,'rows',len(shapes),'ordinary',A.as_expr(),'11',B.as_expr(),'43',C.as_expr(),flush=True)
 wordP.append((A,B,C))
 rowdata=[]
 for (F,G),(p,q) in zip(shapes,pairsOnly,strict=True):
  n,I=balance(p,q,A)
  _,J=balance(p,q,B,11)
  _,K=balance(p,q,C,43)
  allNs.append(n)
  rowdata.append(f'⟨{showcase(F)},{showcase(G)},{n},{I},{J},{K}⟩')
 positions=[[0 for j in range(64)]for i in range(64)]
 for i,j in W[w][2]:positions[i][j]=1
 D={x:i for i,x in enumerate(shapes)}
 for (i,j),x in tab.items():
  code=2+D[x]
  assert code<1024
  positions[i][j]=code
 positions=ar(hex(sum(x*(1024**j)for j,x in enumerate(z)))for z in positions)
 data.append((lean,ar(rowdata),positions,pol(A),pol(B),pol(C)))
x,y,z=[p[0] for p in wordP]
G=x.to_field().gcd(y.to_field())
A,B,_=x.to_field().gcdex(y.to_field())
C,D,F=G.gcdex(z.to_field())
A*=C;B*=C
N=lcm(*(int(c.q)for q in [A,B,D]for c in q.all_coeffs()))
allNs.append(N)
print('common gcd',F,'primitive denom',N,flush=True)
I=idstr((A*N).to_ring(),(B*N).to_ring(),(D*N).to_ring(),0,(F*N).to_ring())
p43=Poly(b**2-b-2,b,domain=ZZ)
_,J=balance(wordP[0][2],wordP[1][2],p43,43)
_,K=balance(wordP[0][1],Poly(0,b,domain=ZZ),Poly(b**10-1,b,domain=ZZ),11)
assert F==Poly(b+1,b,domain=QQ)
commonN=lcm(*allNs)
print('constant factors',factorint(commonN),flush=True)
for index,(k,rows,route,A,B,C) in enumerate(data):
 Path(f'RibbonStationarySurfaceData{index}.lean').write_text(f'''import RibbonStationarySurfaceCore
namespace RibbonStationaryField
set_option maxHeartbeats 0
set_option maxRecDepth 30000
def surf{index} : SurfaceSpec := ⟨{k},{rows},{route},{A},{B},{C}⟩
theorem surfGeom{index} : SurfaceGeom surf{index} := by decide +kernel
theorem surfOrd{index} : ∀ r, surfaceOrdinary surf{index} r {commonN} := by decide +kernel
theorem surfMod{index} : ∀ r, ∀ j, surfaceMod surf{index} r j := by decide +kernel
end RibbonStationaryField
''')
Path('RibbonStationarySurfaceEndData.lean').write_text(''.join(f'import RibbonStationarySurfaceData{i}\n'for i in range(3))+f'''
namespace RibbonStationaryField
open RibbonAffine (mulP)
def commonN : Int := {commonN}
def surfN : Int := {N}
def surfJoin : Id := {I}
def surf11Join : Id := {K}
def surf43Join : Id := {J}
def surf43target : Poly := {pol(p43)}
def surfGcd : Poly := [(0,1,1),(0,0,1)]
theorem surfJoinOK : surfN∣commonN ∧ surfJoin.rhs=mulP (natConst surfN) surfGcd ∧
    surfJoin.valid surf0.normal surf1.normal surf2.normal 0 := by decide +kernel
theorem surf11JoinOK : surf11Join.rhs=surfaceBinom 10 ∧ surf11Join.valid surf0.mod11 [] [] 11 := by decide +kernel
theorem surf43JoinOK : surf43Join.rhs=surf43target ∧ surf43Join.valid surf0.mod43 surf1.mod43 [] 43 := by decide +kernel
end RibbonStationaryField
''')
