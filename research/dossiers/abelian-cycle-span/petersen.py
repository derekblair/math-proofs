from itertools import product
from span_search import *

N,A=step_graph(5,2); ch=gauge(N,A)
G,rank=compute(N,A,ch,words(N,A,{4,8,16}))
bad,states,used=search(G,rank)
assert bad is None
g=sorted({w for row in used for w in [G[row]]},key=lambda w:(len(w),w))
for i in range(len(g)-1,-1,-1):
    W=g[:i]+g[i+1:]
    R,d=compute(N,A,ch,W)
    if search(R,d)[0] is None:g=W
R,d=compute(N,A,ch,g)
res,st,_=search(R,d);assert res is None
S,_=compute(N,A,ch,words(N,A,{4,8}))
assert all(not C for z,C in S)
def ev(p,v,m):return sum(x*y for x,y in zip(p,v))%m
print('tree complement',ch,'complete rows',len(G),'full states',states,'minimal by deletions',len(g),'chart states',st)
print('words',' '.join(''.join(map(str,w)) for w in g))
found=None
for m in range(2,12):
    for V in product(range(m),repeat=d):
        if all(ev(V,z,m) for z,C in S):
            from math import gcd
            if gcd(*V,m)!=1:continue
            witness=next(w for (z,C),w in R.items() if ev(V,z,m)==0 and all(ev(V,x,m)!=0 for x in C))
            found=(m,V,witness)
            break
    if found:break
assert found
print('sharp',found,'short rows',len(S))
json.dump([ch,g,found],open('petersen.json','w'))
