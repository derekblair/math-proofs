from pathlib import Path
from collections import defaultdict
from itertools import combinations
from math import comb
import json
def min_inter(A,B,n):
 # An independent deadline implementation of the exact minimum:
 # schedule B's increasing occupied positions against distinct sites.
 available=set(range(n)); count=0
 for t in sorted(B):
  P=[x for x in available if x<=t]
  if len(P)==0: raise ValueError('deadlines infeasible')
  Q=[x for x in P if x not in A]
  if Q:available.remove(min(Q))
  else:available.remove(min(P));count+=1
 return count
def bits(x,n):return {i for i in range(n) if (x>>i)&1}
def objective(n,p,q):
 def f(n,t):
  if (n-t)%2:return 2*f(n-1,t)
  return sum(comb(n,j)for j in range((n+t)//2,n+1))
 vals=[(f(k,p)*f(n-k,q),k,n-k)for k in range(p,n-q+1)]
 m=max(v[0]for v in vals)
 return m,[r[1:]for r in vals if r[0]==m]
for path in sorted(Path('.').glob('colors-*-2-2.json')):
 n,p,q=map(int,path.stem.split('-')[1:])
 masks={int(a):b for a,b in json.loads(path.read_text()).items()}
 classes=defaultdict(list)
 U={i:bits(i,n)for i in range(1<<n)}
 U={i:A for i,A in U.items() if min_inter(A,A,n)>=max(p,2*len(A)-(n-q))}
 assert set(U)==set(masks), (n,len(U),len(masks))
 for i,c in masks.items():classes[c].append(U[i])
 pairs=0
 for C in classes.values():
  for A,B in combinations(C,2):
   assert min_inter(A,B,n)<max(p,len(A)+len(B)-(n-q))
   pairs+=1
 m,s=objective(n,p,q)
 assert len(classes)==m
 print(n,len(U),len(classes),pairs,s)
