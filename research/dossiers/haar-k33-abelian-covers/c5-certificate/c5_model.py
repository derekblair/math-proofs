from itertools import product
n=5
def adj(u,j):return n+(u+j)%n if u<n else (u-n-j)%n
edges=sorted({(u,adj(u,j)) for u in range(n) for j in range(3)})
p=list(range(2*n)); tree=set()
def find(u):
 while p[u]!=u:u=p[u]
 return u
for u,v in edges:
 if find(u)!=find(v):tree.add((u,v));p[find(u)]=find(v)
cotree=tuple(e for e in edges if e not in tree)
idx={a:i for i,a in enumerate(cotree)}
zero=(0,)*len(cotree)
def step(state,j,p):
 u,a=state;v=adj(u,j);e=(min(u,v),max(u,v))
 if e in idx:
  k=idx[e];a=a[:k]+((a[k]+(1 if u<n else -1))%p,)+a[k+1:]
 return v,a
def words(n,root,p):
 stack=[((),(root,zero))]
 for _ in range(n):stack=[(L+(j,),step(s,j,p)) for L,s in stack for j in range(3) if not L or j!=L[-1]]
 return stack
