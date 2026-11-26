from collections import Counter,defaultdict
from itertools import combinations
from math import gcd
from sympy import symbols,Poly,factor_list
from pathlib import Path
a,b,t=symbols('a b t')
P=Path('../flagship-affine-1729')
W=[]
CANDIDATES=Path(__file__).with_name('candidates-frozen.tsv')
for l in CANDIDATES.read_text().splitlines():
  r,w,*M=l.split();W.append((int(r),w,{tuple(map(int,m.split(','))) for m in M}))
def row(r,w):
  x=y=0;C=Counter();out=[]
  for d in w:
    out.append((r,x,y,C.copy()))
    if d=='2':r^=1
    else:
      s=1 if d=='0' else -1
      if r:C[x,y+min(s,0)]+=s;y+=s
      else:x+=s
  return out
def pairs(R):
  r,w,m=R; A=row(r,w)
  out=[]
  for (i,(r,x,y,p)),(j,(s,X,Y,q)) in combinations(enumerate(A),2):
    if r==s and (i,j) not in m:
      out.append((i,j,x-X,y-Y,{k:p[k]-q[k] for k in p.keys()|q.keys() if p[k]!=q[k]}))
  return out
def norm(L,v):
  z=Counter()
  for d,c in L:z[d]+=c
  z={d:c for d,c in z.items() if c}
  return 0 if not z else sum(c*v**(d-min(z)) for d,c in z.items())
def bip(H):
  X=min(x for x,y in H);Y=min(y for x,y in H)
  return sum(c*a**(x-X)*b**(y-Y) for (x,y),c in H.items())
def slopes(R):
  out=defaultdict(set);z=[]
  for i,j,x,y,H in pairs(R):
    d=gcd(x,y)
    if d:
      if not y:
        assert d<=2
        continue
      x//=d;y//=d
      if y<0:x=-x;y=-y
      z.append(('d',d))
      p=norm(((u*y-v*x,c)for(u,v),c in H.items()),t)
      if not p:out[x,y].add(('ZERO',i,j));continue
      c,F=factor_list(p,t); out[x,y].update([str(f)for f,k in F]);out[x,y].add(abs(int(c)))
    elif not H:out[0,0].add(('ZERO',i,j))
    else:
      c,F=factor_list(bip(H),a,b);out[0,0].update([str(f)for f,k in F]);out[0,0].add(abs(int(c)))
  return sorted(set(z)),dict(out)
if __name__=='__main__':
 print(slopes(W[0]))
