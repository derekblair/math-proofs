"""Independent tiny barrier witness, exhaustive directed shortest paths."""
from collections import defaultdict
from itertools import combinations, product
from heapq import heappop,heappush
q=3; M=2
A=defaultdict(dict)
def e(a,b,w): A[a][b]=w; A[b]
a=lambda i:('a',i)
b=lambda i:('b',i)
s=lambda i:('s',i)
t=lambda i:('t',i)
H=('H',)
for i in range(q):
 for x,y,w in [(s(i),a(i),1),(b(i),t(i),1),(a(i),H,4),(H,b(i),4),(a(i),b(i),8),(s(q),b(i),1),(b(i),a(i),1),(a(i),t(q),1)]: e(x,y,w)
e(s(q),t(q),3)
for i,j in combinations(range(q),2):
 for m in range(M):
  U,V=('u',i,j,m),('v',i,j,m)
  for x,y,w in [(H,U,1),(U,H,1),(U,V,1),(V,U,1),(a(j),V,2),(V,b(i),2)]: e(x,y,w)
def routes(i,current,P,W):
 if current==t(i):
  if W==(10 if i!=q else 3): yield P
  assert not W<(10 if i!=q else 3)
 else:
  for y,w in A[current].items():
   if y not in P and W+w<=(10 if i!=q else 3):
    yield from routes(i,y,P+(y,),W+w)
routes=[list(routes(i,s(i),(s(i),),0)) for i in range(q+1)]
supports=[set(x for P in R for x in P) for R in routes]
edges=[set((x,y) for P in R for x,y in zip(P,P[1:])) for R in routes]
assert set().union(*edges)=={(x,y) for x,N in A.items() for y in N}
for i,j in combinations(range(q),2):
 for m in range(M):
  U,V=('u',i,j,m),('v',i,j,m)
  assert (U,V) in edges[i] and (V,U) in edges[j]
C=set(A)-{f(i) for f in (s,t) for i in range(q+1)}
def component(x):
 L={x}; Q=[x]
 while Q:
  for y in A[Q.pop()]:
   if y in C-L: Q.append(y);L.add(y)
 return L
assert all(component(x)==C for x in C)
good=[P for P in product(*routes) if sum(map(len,P))==len(set().union(*map(set,P)))]
conflicts=set().union(*(supports[i]&supports[j] for i,j in combinations(range(q),2)))
assert good and all(P[q]==(s(q),t(q)) for P in good)
assert min(len(set().union(*map(set,P))&conflicts) for P in good)==0
print(len(A),len(C),list(map(len,routes)),len(good),len(conflicts))
