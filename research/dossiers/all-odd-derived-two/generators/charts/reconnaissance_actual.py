from pathlib import Path
from collections import defaultdict
from itertools import combinations, product
from json import dumps

pdir=Path('.')
W=[]
for s in (pdir/'actual_spec.tsv').read_text().splitlines():
    r,w,*M=s.split()
    W.append((int(r),w,{tuple(map(int,m.split(','))) for m in M}))
S={(p,a,b) for ln in (pdir/'failed-field-triples.txt').read_text().splitlines() if ln.startswith('unsolved') for p,a,b in [tuple(map(int,ln.split()[1:]))]}
S=sorted(S | {(p,b,a) for p,a,b in S})
def collision(wt,p,a,b,da=0,db=0):
    side,w,M=wt
    ai=pow(a,-1,p);bi=pow(b,-1,p)
    A=(a,da);B=(b,db);Ai=(ai,-da*ai*ai%p);Bi=(bi,-db*bi*bi%p)
    def mul(u,v):return u[0]*v[0]%p,(u[0]*v[1]+u[1]*v[0])%p
    def add(u,v):return (u[0]+v[0])%p,(u[1]+v[1])%p
    def neg(u):return -u[0]%p,-u[1]%p
    m,t=(1,0),(0,0); seen=defaultdict(list); miss=set()
    for i,c in enumerate(w):
        key=(side,m,t)
        miss.update((j,i) for j in seen[key] if (j,i) not in M)
        seen[key].append(i)
        if c=='2':side^=1;continue
        tau=int((a!=1)==bool(side))
        if c=='0':
            if tau:t=add(t,m)
            m=mul(m,B if side else A)
        else:
            m=mul(m,Bi if side else Ai)
            if tau:t=add(t,neg(m))
    assert (side,m,t)==(wt[0],(1,0),(0,0))
    return miss
bad=list(S)
tab=[[collision(w,*z) for z in bad]for w in W]
print('single bad closed under swap:',bad,flush=True)
assert all(all(row[i] for row in tab) for i in range(len(bad)))
pair_fail=[]
for i,j in combinations(range(len(bad)),2):
    if all(row[i]&row[j] for row in tab):
        pair_fail.append((bad[i],bad[j],min(len(row[i]&row[j])for row in tab)))
print('pair fail',len(pair_fail),'of',len(bad)*(len(bad)-1)//2,pair_fail,flush=True)
n=0;failed=[]
for p,a,b in bad:
    for da,db in [(0,1)]+[(1,k)for k in range(p)]:
        n+=1
        if all(collision(w,p,a,b,da,db) for w in W):
            failed.append((p,a,b,da,db))
print('projective jet fail',len(failed),'of',n,failed,flush=True)
