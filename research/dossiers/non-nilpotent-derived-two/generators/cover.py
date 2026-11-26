from symbolic_d2 import *
from sympy import resultant, factorint, expand, Rational, cyclotomic_poly
from functools import lru_cache
from json import dumps
here=Path(__file__).parent
P0=145
@lru_cache(None)
def raw(q):return pairs(W[q])
def remove23(x):
 for d in (2,3):
  while x and x%d==0:x//=d
 return x
ignoret={'t','t - 1','t + 1','t**2 + 1','t**2 + t + 1','t**2 - t + 1'}
ignorem={'a','b','a - 1','a + 1','b + 1','a**2 - a + 1','b**2 - b + 1','a**2 + a + 1','b**2 + b + 1'}
@lru_cache(None)
def table(q,u,v):
 C=set()
 for i,j,x,y,H in raw(q):
  d=remove23(abs(v*x-u*y))
  if d==1:continue
  f=norm(((s*v-z*u,c) for (s,z),c in H.items()),t)
  C.add((d,Poly(f,t)))
 return C
@lru_cache(None)
def R(f,g):return int(resultant(f,g)) if not g.is_zero else 0
def eval_t(q,f,u,v):
 exc=set()
 for d,g in table(q,u,v):
  r0=abs(R(f,g));r1=abs(R(f,Poly(t**d-1,t))) if d else 0
  r=gcd(r0,r1)
  if not r:return None
  exc.update(i for i in factorint(r) if i not in (2,3))
 return exc
def powmod(P,n,g):
 r=Poly(1,P.gen,modulus=P.get_modulus()); P=P.rem(g)
 while n:
  if n&1:r=(r*P).rem(g)
  P=(P*P).rem(g);n//=2
 return r
def t_extras(q,f,u,v,exc):
 out=[]
 for p in exc:
  fp=f.set_modulus(p)
  if fp.is_zero:
   out.append((p,'zero'));continue
  for g,_ in factor_list(fp)[1]:
   if g==Poly(t,t,modulus=p):continue
   o=p**g.degree()-1
   for k in factorint(o):
    while o%k==0 and powmod(Poly(t,t,modulus=p),o//k,g)==Poly(1,t,modulus=p):o//=k
   if o==1 or remove23(o)!=o: continue
   if any(P.set_modulus(p).rem(g).is_zero and (not d or Poly(t**d-1,t,modulus=p).rem(g).is_zero) for d,P in table(q,u,v)):
    out.append((p,str(g.as_expr())))
 return out
def t_branches(P0):
 D=[]
 for i,j,x,y,H in raw(P0):
  d=gcd(x,y)
  if not d:continue
  if remove23(d)!=1:raise ValueError(('large gcd',d))
  if not y:continue
  x//=d;y//=d
  if y<0:x=-x;y=-y
  P=norm(((u*y-v*x,c) for (u,v),c in H.items()),t)
  if not P:raise ValueError(('zero',i,j))
  c,F=factor_list(P,t)
  if remove23(abs(c))!=1:raise ValueError(('constant',c))
  D.extend((x,y,Poly(f,t)) for f,_ in F if str(f) not in ignoret)
 return sorted(set(D),key=str)
if __name__=='__main__':
 import sys
 if len(sys.argv)>1:P0=int(sys.argv[1])
 branches=t_branches(P0);print('base',P0,len(branches),flush=True)
 for u,v,f in branches:
  tbest=None
  for q in range(len(W)):
   e=eval_t(q,f,u,v)
   if e is None:continue
   extra=t_extras(q,f,u,v,e)
   if any(p!=11 for p,_ in extra):continue
   tbest=q, sorted(e),extra
   break
  print(u,v,f.as_expr(),tbest,flush=True)
