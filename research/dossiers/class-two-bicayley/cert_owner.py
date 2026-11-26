#!/usr/bin/env python3
from functools import reduce
from pathlib import Path
s=Path('half_scan.py').read_text()
exec(s.split('p=7')[0])
p=11
a=(1,0,1,0,0,0); A=inv(a,p)
b=(0,1,1,0,0,0); B=inv(b,p)

def step(s,q):
 side,x=s
 if q==2:return (1-side,x)
 return (side,mul(x,((a,A),(b,B))[side][q],p))
def ends(n,u,q):
 if n==0:return [u]
 return [v for r in range(3) if r!=(1,0,2)[q] for v in ends(n-1,step(u,r),r)]
def key(v):
 return reduce(lambda k,x: 11*k+x,v[1],v[0])
def groups(h,s):
 return [list(map(key,ends(h-1,step((s,E),q),q))) for q in range(3)]
def fits(t,s,m):
 groups_=[{x%m for x in u} for u in groups(t,s)]
 return all(not groups_[i]&groups_[j] for i in range(3) for j in range(i))
for h in (2,4,8):
 for side in (0,1):
  m=next(k for k in range(4,1000000) if fits(h,side,k))
  masks=[sum(1<<i for i in {k%m for k in g}) for g in groups(h,side)[:2]]
  print(h,side,m,*(hex(mask) for mask in masks))
