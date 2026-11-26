from cover import *
from ast import literal_eval
from itertools import chain
from math import lcm
@lru_cache(None)
def gcdex_pair(f,g):
 if g.is_zero:return (0,0,0,0)
 u,v,h=f.gcdex(g)
 if h.degree()!=0:return (0,0,0,0)
 u/=h.LC();v/=h.LC()
 L=lcm(*(int(c.q) for c in chain(Poly(u,t).all_coeffs(),Poly(v,t).all_coeffs())))
 return L,Poly(L*u,t),Poly(L*v,t),h
def bezout(c,d):
 if not c:return d,0,1
 if not d:return c,1,0
 g,i,j=__import__('sympy').gcdex(c,d)
 # SymPy gcdex returns (S,T,G)
 return int(j),int(g),int(i)
def cert(f,g,h):
 r,A,B,_=gcdex_pair(f,g)
 s,C,D,_=gcdex_pair(f,h)
 n,i,j=bezout(r,s)
 assert n
 assert (i*A+j*C)*f+(i*B)*g+(j*D)*h==n
 return n,Poly(i*A+j*C,t),Poly(i*B,t),Poly(j*D,t)
def fmt(P):return list(map(int,reversed(P.all_coeffs()))) if not P.is_zero else []
def rowcert(u,v,f,q):
 records=[]
 vals=sorted(table(q,u,v),key=str)
 for d,g in vals:
  h=Poly(t**d-1,t)
  n,A,B,C=cert(f,g,h)
  records.append([d,fmt(g),n,fmt(A),fmt(B),fmt(C)])
 return records
rows=[]
for l in open('cover145.fast.log').read().splitlines()[1:]:
 u,v,end=l.split(maxsplit=2);u=int(u);v=int(v);k=end.index(' (')
 f=Poly(end[:k],t);q,e,z=literal_eval(end[k+1:])
 try:
  ds=rowcert(u,v,f,q)
 except Exception as E:
  print(l,E);raise
 assert {p for i in ds for p in factorint(i[2]) if p not in (2,3)}<=set(e)
 rows.append([u,v,fmt(f),q,ds])
Path('slope-integer.json').write_text(dumps(rows,separators=(',',':')))
print('finished',len(rows),'branches',sum(len(r[-1]) for r in rows),'identities')
