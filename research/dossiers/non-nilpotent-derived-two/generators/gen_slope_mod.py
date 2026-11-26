from cover import *
from json import loads,dumps
from math import lcm
from sympy import ZZ, GF
def poly(a,P):return Poly(sum(v*t**i for i,v in enumerate(a)if v),t,modulus=P)
def coeff(p):return list(map(int,reversed(p.all_coeffs()))) if not p.is_zero else []
def dv(P,F):
 return Poly(t**F-1,t,modulus=P)
def gx(f,g):
 if g.is_zero:return f.monic(),Poly(f.LC()**-1,t,modulus=f.get_modulus()),g
 return f.gcdex(g)[::-1]
def bez(f,g,h):
 p=int(f.get_modulus())
 # Return monic gcd and three linear combination multipliers
 def gx(f,g):
  if f.is_zero and g.is_zero:return (f,f,f)
  if f.is_zero:return (g.monic(),f,Poly(pow(int(g.LC()),-1,p),t,modulus=p))
  if g.is_zero:return (f.monic(),Poly(pow(int(f.LC()),-1,p),t,modulus=p),g)
  u,v,d=f.gcdex(g);return d,u,v
 d,u,v=gx(f,g)
 e,x,y=gx(d,h)
 assert e==x*u*f+x*v*g+y*h
 return e,x*u,x*v,y
def exactord(F,p):
 q=Poly(t,t,modulus=p)
 order=p**F.degree()-1
 for z in factorint(order):
  while order%z==0 and powmod(q,order//z,F)==Poly(1,t,modulus=p):order//=z
 return order
records=[]
for u,v,f,k,rs in loads(Path('slope-integer.json').read_text()):
 rec={}
 pp={p for d,g,n,*_ in rs for p in factorint(n) if p!=2}
 for p in sorted(pp):
  F=poly(f,p);pairs=[]
  for rid,(d,g,n,A,B,C) in enumerate(rs):
   if n%p:continue
   G=poly(g,p);H=dv(p,d)
   d,X,Y,Z=bez(F,G,H)
   assert not d.is_zero
   fac=[]
   for B,mul in factor_list(d)[1]:
    if B==Poly(t,t,modulus=p):o=0
    else:o=exactord(B,p)
    fac.extend([[coeff(B),o]]*mul)
   pairs.append([rid,coeff(d),coeff(X),coeff(Y),coeff(Z),fac])
  rec[p]=pairs
 records.append(rec)
Path('slope-modular.json').write_text(dumps(records,separators=(',',':')))
print('rows',sum(len(rs) for d in records for rs in d.values()))
print('detected exponent max',max(o for d in records for l in d.values() for *_,f in l for _,o in f))
print('eligible primes',sorted({p for d in records for p,L in d.items()for *_,fs in L for f,o in fs if o>1 and remove23(o)==o}))
