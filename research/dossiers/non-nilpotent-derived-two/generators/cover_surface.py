from cover import *
from sympy import ZZ
@lru_cache(None)
def table_s(q,a0):
 C=set()
 for i,j,x,y,H in raw(q):
  den,P=Poly(norm(((z,c*a0**s) for (s,z),c in H.items()),b),b,domain='QQ').clear_denoms(convert=True)
  if y<0:x=-x;y=-y
  if y:
   _,Q=Poly(a0**x*b**y-1,b,domain='QQ').clear_denoms(convert=True)
  else:
   _,Q=Poly(a0**x-1,b,domain='QQ').clear_denoms(convert=True)
  C.add((Q,P))
 return C
def eval_s(q,a0):
 exc=set()
 for Q,P in table_s(q,a0):
  if Q.is_zero:
   if P.degree()!=0:return None
   r=abs(int(P.LC()))
  elif P.is_zero:
   if Q.degree()!=0:return None
   r=abs(int(Q.LC()))
  else:r=abs(R(Q,P))
  if not r:return None
  exc.update(i for i in factorint(r) if i not in (2,3))
 return exc
def s_extras(q,a0,exc):
 out=[]
 for p in exc:
  av=(int(a0.p)*pow(int(a0.q),-1,p))%p;o=p-1
  if av in (0,1):continue
  for k in factorint(o):
   while o%k==0 and pow(av,o//k,p)==1:o//=k
  if remove23(o)!=o:continue
  for Q,P in table_s(q,a0):
   g=Q.set_modulus(p).gcd(P.set_modulus(p))
   if g.is_zero:out.append((p,'zero'));continue
   for L,_ in factor_list(g)[1]:
    if L==Poly(b,b,modulus=p):continue
    oo=p**L.degree()-1
    for k in factorint(oo):
     while oo%k==0 and powmod(Poly(b,b,modulus=p),oo//k,L)==Poly(1,b,modulus=p):oo//=k
    if remove23(oo)==oo:out.append((p,str(L.as_expr())))
 return sorted(set(out))
if __name__=="__main__":
 for a0 in [Rational(-1,2),Rational(-2)]:
  for q in range(len(W)):
   e=eval_s(q,a0)
   if e is None:continue
   E=s_extras(q,a0,e)
   if all(p==11 for p,_ in E):
    print(a0,q,sorted(e),E,flush=True);break
  else:print(a0,'NONE',flush=True)
