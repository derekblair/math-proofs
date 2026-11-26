from functools import reduce
from itertools import product
p=11
def op(a,b):
 x,y,z,t,u,v,w,r,s,f=a
 X,Y,Z,T,U,V,W,R,S,F=b
 return tuple(k%p for k in (x+X,y+Y,z+Z,t+T,u+U+x*Y,v+V+y*Z,w+W+z*T,r+R+x*V+u*Z,s+S+y*W+v*T,f+F+x*S+u*W+r*T))
def power(a,n):
 res=(0,)*10
 for _ in range(n):res=op(res,a)
 return res
def inv(a):return power(a,p-1)
a=(1,0,1,1,0,0,0,0,0,0)
b=(0,1,1,1,0,0,0,0,0,0)
A=inv(a);B=inv(b)
def comm(a,b):return op(op(op(a,b),inv(a)),inv(b))
c=comm(A,B);u=comm(c,a);v=comm(c,b)
assert any(any(comm(g,h)) for g,h in product((u,v),(a,b)))
E=(0,)*10
def step(s,j):
 side,g=s
 if j==2:return (1-side,g)
 return (side,op(g,((a,A),(b,B))[side][j]))
def ends(n,u,q):
 if not n:return [u]
 return [v for j in range(3) if j!=(1,0,2)[q] for v in ends(n-1,step(u,j),j)]
def key(v):
 return reduce(lambda k,x:p*k+x,v[1],v[0])
def table(h,s):
 return [list(map(key,ends(h-1,step((s,E),q),q))) for q in range(3)]
for h in (2,4,8):
 for s in (0,1):
  groups=table(h,s)
  assert len(set(sum(groups,[])))==3*2**(h-1)
  for m in range(4,100000):
   dig=[{x%m for x in q} for q in groups]
   if any(dig[i]&dig[j] for i in range(3) for j in range(i)):continue
   mask=[sum(1<<i for i in v) for v in dig[:2]]
   print(h,s,m,*(hex(x) for x in mask))
   break
