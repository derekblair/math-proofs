from split_check import dist,allshort,states,INF
from random import Random
from itertools import product
from collections import defaultdict

def findroute(n,A,ST,F,control):
    k=len(ST)
    labels=[allshort(n,A,s,t) for s,t in ST]
    answer=states([P for _,P in labels])
    if any(not P for _,P in labels):return
    original=[{(u,v) for p in P for u,v in zip(p,p[1:])} for _,P in labels]
    # Outer comparison still uses all paths; dropping other terminals is safe.
    for i in range(k):
        other={x for j,st in enumerate(ST) if j!=i for x in st}
        original[i]={e for e in original[i] if not other.intersection(e)}
    U={e:A[e] for e in set().union(*original)}
    Ds=[dist(n,U,v)[0] for v in range(n)]
    R=set(range(n));comps=[]
    while R:
        x=min(R);T={y for y in R if Ds[x][y]<INF and Ds[y][x]<INF}
        comps.append(T);R-=T
    ordered=[]
    while comps:
        i=next(i for i,C in enumerate(comps) if all(u in C or v not in C for u,v in U))
        ordered.append(comps.pop(i))
        # Above condition must ignore already processed tails.
        U={e:w for e,w in U.items() if e[0] not in ordered[-1]}
    ci={x:i for i,C in enumerate(ordered) for x in C}
    d=[dist(n,A,s)[0] for s,t in ST]
    layers={tuple(s for s,t in ST)}
    idle=-1
    for index,C in enumerate(ordered):
        cf=sorted(C&F)
        if len(C)>1:control[1]+=1
        # plus clones are the original integer IDs; minus clones add n.
        tail=lambda v:v
        head=lambda v:v+n if v in cf else v
        V=set(C)|{v+n for v in cf}
        B={(tail(u),head(v)) for e in original for u,v in e if u in C and v in C}
        order=[]
        while V:
            x=min(x for x in V if all(b!=x or a not in V for a,b in B));order.append(x);V.remove(x)
        rank={x:i for i,x in enumerate(order)}
        schemas=defaultdict(set);updates=set()
        for x in layers:
            I=tuple(i for i,v in enumerate(x) if v in C)
            if not I:updates.add(x);continue
            for H in product((-1,)+I,repeat=len(cf)):
                owner=dict(zip(cf,H)); targets=[None]*k; slots=list(range(k))
                Z=list(x);valid=True
                for i in I:
                    a,b=x[i],ST[i][1]
                    if a in cf and owner[a]!=i or b in cf and owner[b]!=i:valid=False;break
                    f=sorted((u for u in cf if owner[u]==i and u not in (a,b)),key=lambda u:d[i][u])
                    if a==b:
                        if f:valid=False;break
                        if a in cf:Z[i]=idle;continue
                    Q=[a]+f+([b] if b in C else [])
                    if a!=b and any(d[i][v]<=d[i][u] for u,v in zip(Q,Q[1:])):valid=False;break
                    Z[i]=tail(Q[-2] if b in C and f else Q[-1] if b not in C else a)
                    targets[i]=head(b) if b in C else -2 # -2 = flexible exit
                    for u,v in zip([a]+f[:-1],f):
                        Z.append(tail(u));targets.append(head(v));slots.append(i)
                if not valid or len([u for u in Z if u!=idle])!=len(set(u for u in Z if u!=idle)):continue
                schemas[(tuple(targets),tuple(slots))].add(tuple(Z))
        for (T,L),start in schemas.items():
            seen=set(start);Q=list(start)
            for Z in Q:
                current=[(rank[v],p) for p,v in enumerate(Z) if T[p] is not None and v in rank]
                if not current:
                    assert all(x==idle for x in Z[k:])
                    updates.add(Z[:k]);continue
                _,p=min(current); i=L[p];u=Z[p]; control[2]+=1
                if u==T[p]:out=[idle]
                elif u>=n:out=[]
                else:
                    out=[]
                    for a,b in original[i]:
                        if a!=u:continue
                        if b in C:out.append(head(b))
                        elif T[p]==-2 and ci[b]>index:out.append(b)
                for v in out:
                    if v!=idle and v in Z:continue
                    H=Z[:p]+(v,)+Z[p+1:]
                    assert len(H)<=k+len(cf)
                    if H not in seen:seen.add(H);Q.append(H)
        layers=updates
    assert ((idle,)*k in layers)==(answer is not None)
    control[0]+=1

rng=Random(53);control=[0,0,0]
for r in range(500):
    n=9;F=set(rng.sample(range(n),rng.randrange(4)))
    A={(u,v):rng.randrange(1,5) for u in range(n) for v in range(n)
       if u!=v and (u<v or u in F or v in F) and rng.randrange(3)==0}
    st=rng.sample(range(n),6)
    findroute(n,A,list(zip(st[:3],st[3:])),F,control)
# Up to three parallel 2-cycles are all present in shortest-path supports;
# each has one feedback vertex, with opposing shortest routes and private alternatives.
for cutmask in range(8):
    A={(0,3):3,(1,4):3,(2,5):1}
    for v in range(3):
        x,y=6+2*v,7+2*v
        A[x,y]=1
        if cutmask>>v&1:A[y,x]=1
        for u in (0,1):
            A[u,x+u]=1;A[x+u,4-u]=1
    findroute(12,A,[(0,3),(1,4),(2,5)],{7,9,11},control)
print('exact SCC sweep vs brute case count / cyclic components / active states:',*control)
