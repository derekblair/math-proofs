from itertools import combinations
V=range(7)
cyc={tuple(sorted((i,(i+1)%5))) for i in range(5)}
extras=[(i,j) for i,j in combinations(V,2) if j>=5]
tris=[{(i,j),(i,k),(j,k)} for i,j,k in combinations(V,3)]
def checked(es):
 return not any(t<=es for t in tris)
def maximal(es):
 return all(not checked(es|{e}) for e in extras if e not in es)
bank=[]
for m in range(1<<len(extras)):
 es=cyc|{e for k,e in enumerate(extras) if (m>>k)&1}
 if checked(es) and maximal(es): bank.append((m,es))
print(len(bank),[m for m,_ in bank])
mx=0
for m,es in bank:
 ed=sorted(es)
 mx=max(mx,len(ed))
 for co in range(1<<len(ed)):
  assert any(all(not ((col>>i)&1==(col>>j)&1==(co>>k)&1) for k,(i,j) in enumerate(ed)) for col in range(128)),(m,co)
print(mx)
def covers(es):
 E=sorted(es)
 unseen=set(range(1<<len(E)))
 C=[{a for a in unseen if all(not ((s>>i)&1==(s>>j)&1==(a>>k)&1) for k,(i,j) in enumerate(E))} for s in range(128)]
 choose=[]
 while unseen:
  s=max(range(128),key=lambda k:len(C[k]&unseen))
  choose.append(s)
  unseen.difference_update(C[s])
 return choose
out=[(m,sorted(es),covers(es)) for m,es in bank]
print('cover sizes',[len(c) for _,_,c in out])
C7={tuple(sorted((i,(i+1)%7))) for i in range(7)}
print('C7',covers(C7))
print([(m,c[0],len([1 for i,j in es if ((c[0]>>i)&1)==((c[0]>>j)&1)])) for m,es,c in out])
from collections import defaultdict
def canon(es):
 return min(tuple(sorted(tuple(sorted((p[i],p[j]))) for i,j in es))
 for k in range(5) for d in [1,-1] for u in [0,1]
 for p in [[(k+d*i)%5 for i in range(5)]+[5+u,6-u]])
part=defaultdict(list)
for m,es,c in out: part[canon(es)].append((m,c[0]))
print('orbits',list(part.values()))
