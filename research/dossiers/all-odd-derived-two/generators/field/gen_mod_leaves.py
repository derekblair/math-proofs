from gen_slope_mod import *
S=loads(open('slope-modular.json').read())
T=sorted({(int(p),tuple(f),o) for D in S for p,L in D.items() for *_,fs in L for f,o in fs})
def intpoly(v):return Poly(sum(c*t**i for i,c in enumerate(v)),t,domain=ZZ)
def exact(F,G,p): 
 Q,R=F.div(G)
 assert R.is_zero
 return Q
def moddebt(F,p):
 return F.exquo_ground(p)
R=[]
for p,f,o in T:
 if o%2==1:
  assert p in (7,11,13,43) and len(f)==2 and f[1]==1
  R.append([p,f,[-f[0]%p]]);continue
 assert o>0 and remove23(o)<o
 F=poly(f,p);q=(dv(p,o)).exquo(F)
 FI=intpoly(f);QI=intpoly(coeff(q))
 db=moddebt(Poly(t**o-1,t)-FI*QI,p)
 d=remove23(o)
 J=dv(p,d)
 A,B,H=F.gcdex(J)
 assert H==Poly(1,t,modulus=p)
 AI=intpoly(coeff(A));BI=intpoly(coeff(B))
 db2=moddebt(Poly(1,t)-AI*FI-BI*Poly(t**d-1,t),p)
 R.append([p,f,[o,d,coeff(QI),coeff(db),coeff(AI),coeff(BI),coeff(db2)]])
Path('slope-leaves.json').write_text(dumps(R,separators=(',',':')))
print('leaves',len(R))
