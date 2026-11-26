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

rng=random.Random(404)
for p in (3,5,7,11,17,31):
 # Degree-one generators only first, then a controlled collection of full rows.
 candidates=[((1,0,1,0,0,0),(0,1,k,0,0,0)) for k in range(p)]
 candidates+=[(tuple(rng.randrange(p) for _ in range(6)),tuple(rng.randrange(p) for _ in range(6))) for _ in range(30)]
 for a,b in candidates:
  if a==E or b==E: continue
  r=[n for n in [4,8,16] if any(xy_cycle(a,b,p,n,s) for s in (0,1))]
  if not r:
   assert any(xy_cycle(a,b,p,32,s) for s in (0,1))
   print("SHARP",p,a,b,flush=True)
   break
 else:
  print("no sharp control",p,flush=True)
