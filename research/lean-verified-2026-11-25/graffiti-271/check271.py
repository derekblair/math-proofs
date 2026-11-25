from itertools import combinations

def stats(n,E):
 A=[0]*n
 for i,j in E:A[i]|=1<<j;A[j]|=1<<i
 def reach(i):
  D=[-1]*n;D[i]=0; q=[i]
  for u in q:
   B=A[u]
   while B:
    b=B&-B;B-=b;v=b.bit_length()-1
    if D[v]<0:D[v]=D[u]+1;q.append(v)
  return D
 d0=reach(0)
 if -1 in d0:return None
 m=max(a.bit_count() for a in A);vs=[i for i,a in enumerate(A) if a.bit_count()==m]
 a=max(reach(v)[w] for v in vs for w in vs)
 for b in range(2,n+1):
  for S in combinations(range(n),b):
   D=0
   for v in S:D|=A[v]
   if D==(1<<n)-1:return b,a,max(max(reach(i)) for i in range(n))
 raise AssertionError(E)
cyc=stats(4,[(0,1),(1,2),(2,3),(3,0)])
path=stats(4,[(0,1),(1,2),(2,3)])
assert cyc==(2,2,2),cyc
assert path==(2,1,3),path
print('Sharp C4 and ordinary-diameter P4 controls:',cyc,path)
total=0
for n in range(2,7):
 E=list(combinations(range(n),2));ct=0
 for mask in range(1<<len(E)):
  st=stats(n,[e for i,e in enumerate(E) if mask>>i&1])
  if st is None:continue
  ct+=1
  s,d,_=st
  assert 2*d<=s*s,(n,mask,st)
 total+=ct
 print(n,ct)
assert total==27475,total
print(total,'connected labeled graphs checked')
