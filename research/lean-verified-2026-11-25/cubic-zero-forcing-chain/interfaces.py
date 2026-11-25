from itertools import combinations
def block(m):
 G=[set() for _ in range(6+m)]
 for i in range(3):
  for j in range(3,6):
   if i<m and j==i+3:
    G[i].add(6+i);G[j].add(6+i);G[6+i].update((i,j))
   else:G[i].add(j);G[j].add(i)
 return G
for m in [1,2]:
 G=block(m);P=set(range(6,6+m));allv=set(range(6+m))
 def close(s,blockOutgoing=False):
  while 1:
   f={next(iter(G[i]-s)) for i in s if len(G[i]-s)==1 and (not blockOutgoing or i!=6+m-1)}
   if not f:return s
   s|=f
 print('block',m,'first',next(s for s in combinations(allv,4) if close(set(s),True)==allv))
 print('block',m,'using-left',next(s for s in combinations(allv-{6},3) if close(set(s)|{6},m==2)==allv))
 for k in (2,3):
  result={}
  for D in map(set,combinations(allv,k)):
   N=D.union(*(G[i] for i in D))
   if not set(range(6))<=N:continue
   encode=lambda i:2 if i in D else 1 if i in N else 0
   result.setdefault(tuple(encode(i) for i in sorted(P)),[]).append(sorted(D))
  print(k,result)
def seq(G,s,blocked):
 s=set(s);R=[]
 while len(s)<len(G):
  pair=next(((i,next(iter(G[i]-s))) for i in sorted(s-set(blocked)) if len(G[i]-s)==1),None)
  if pair is None:return None
  R.append(pair);s.add(pair[1])
 return R
for m,S,no in [(1,[0,1,3,4],[6]),(2,[0,1,4,6],[7]),(1,[0,1,4,6],[])]:
 print('forcing schedule',m,S,seq(block(m),S,no))
