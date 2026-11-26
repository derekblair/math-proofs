#!/usr/bin/env python3
import itertools, random

def mul(a,b,p):
 x,y,z,u,v,w=a
 X,Y,Z,U,V,W=b
 return ((x+X)%p,(y+Y)%p,(z+Z)%p,(u+U+x*Y)%p,(v+V+y*Z)%p,(w+W+x*V+u*Z)%p)
def inv(a,p):
 x,y,z,u,v,w=a
 return ((-x)%p,(-y)%p,(-z)%p,(-u+x*y)%p,(-v+y*z)%p,(-w+x*v+u*z-x*y*z)%p)
E=(0,0,0,0,0,0)
def xy_cycle(a,b,p,n,side):
 A=inv(a,p); B=inv(b,p)
 start=(side,E)
 def step(v):
  l,g=v
  pos,neg=(a,A) if l==0 else (b,B)
  return ((l,mul(g,pos,p)),(l,mul(g,neg,p)),(1-l,g))
 def go(path):
  if len(path)==n: return path if start in step(path[-1]) else None
  for v in step(path[-1]):
   if v not in path:
    r=go(path+(v,))
    if r:return r
  return None
 return go((start,))

p=7
a=(1,0,1,0,0,0)
b=(0,1,1,0,0,0)
A=inv(a,p); B=inv(b,p)
for side0 in (0,1):
 for n in (2,4,8):
  d={}
  stack=[(((side0,E),),())]
  c=0
  while stack:
   path,w=stack.pop(); side,g=path[-1]
   if len(w)==n:
    d.setdefault(path[-1],[]).append((path,w)); c+=1
    continue
   for t,v in enumerate(((side,mul(g,a if side==0 else b,p)),(side,mul(g,A if side==0 else B,p)),(1-side,g))):
    if v not in path:stack.append((path+(v,),w+(t,)))
  pairs=[(u,v) for vals in d.values() for i,u in enumerate(vals) for v in vals[i+1:]]
  print(side0,n,'paths',c,'clashes',len(pairs),'different first',sum(u[1][0]!=v[1][0] for u,v in pairs),'seam disjoint',sum(not set(u[0][1:-1])&set(v[0][1:-1]) for u,v in pairs))
  print([(u[1],v[1]) for u,v in pairs[:6]])
