from collections import deque
import json
g,_,(p,w,s)=json.load(open('petersen.json'))
G=[set() for _ in range(50)]
for i in range(5):
 for u,v in ((i,(i+1)%5),(i+5,(i+2)%5+5),(i,i+5)):
  z=dict(zip(map(tuple,g),w))
  a=z.get((u,v),-z.get((v,u),0))
  for l in range(p):
   U=u+10*l;V=v+10*((l+a)%p)
   G[U].add(V);G[V].add(U)
assert all(len(A)==3 for A in G)
Q={0}
for _ in range(50):Q.update(x for i in list(Q) for x in G[i])
assert len(Q)==50
counts={}
for d in (4,8,16):
 total=0
 for u in range(10): # deck-translation symmetry
  def go(v,a,path):
   if len(path)==d:
    if v in G[u]:
     nonlocal_add[0]+=1
   else:
    for x in G[v]-a:
     go(x,a|{x},path+[x])
  nonlocal_add=[0];go(u,{u},[u]);total+=nonlocal_add[0]
 counts[d]=total
assert counts[4]==counts[8]==0 and counts[16]>0
print(counts)
