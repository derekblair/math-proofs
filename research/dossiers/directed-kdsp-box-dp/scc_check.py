from functools import lru_cache
from itertools import product
from random import Random

def fw(n,A):
    B=[[float('inf')]*n for _ in range(n)]
    for i in range(n): B[i][i]=0
    for u,v,w in A:B[u][v]=min(B[u][v],w)
    for r in range(n):
        for i in range(n):
            for j in range(n): B[i][j]=min(B[i][j],B[i][r]+B[r][j])
    return B

counters=[0,0,0,0]
def both(n,A,ST,do_brute=True):
    B=fw(n,A); k=len(ST)
    if len({v for i,(s,t) in enumerate(ST) for v in set((s,t))})!=sum(len(set(P)) for P in ST):return False
    if any(B[s][t]==float('inf') for s,t in ST):return False
    D=[{(u,v,w) for u,v,w in A if B[s][u]+w+B[v][t]==B[s][t]} for s,t in ST]
    Adj=[{u:{v for x,v,w in E if x==u} for u in range(n)} for E in D]
    U=set().union(*D)
    D0=fw(n,U)
    R=set(range(n)); C=[]
    while R:
        root=min(R); S={y for y in R if D0[root][y]<float('inf') and D0[y][root]<float('inf')}
        C.append(S); R-=S
    leaf=[]
    while C:
        j=next(i for i,S in enumerate(C) if all(not(v in S and u in Q) for h,Q in enumerate(C) if h!=i for u,v,w in U))
        leaf.append(C.pop(j))
    ci={u:i for i,C in enumerate(leaf) for u in C}
    local_group=[]
    for C in leaf:
        loc=sorted(C); idx={x:j for j,x in enumerate(loc)}
        U0={(idx[u],idx[v],w) for u,v,w in U if u in C and v in C}
        E0=[{(idx[v],idx[u],-w) for u,v,w in E if u in C and v in C} for E in D]
        act=[e for e in E0 if e]
        g=[0]
        for mask in range(1,1<<len(act)):
            q=mask;b=k
            while q:
                F=fw(len(C),U0.union(*(e for i,e in enumerate(act) if q>>i&1)))
                if all(F[j][j]>=0 for j in range(len(C))):b=min(b,1+g[mask^q])
                q=(q-1)&mask
            g.append(b)
        local_group.append(g[-1])
    if not do_brute:return max(local_group)
    @lru_cache(None)
    def occ(i,x,y,mask):
        if not (mask>>x&1 and mask>>y&1): return False
        if x==y:return True
        return any(occ(i,v,y,mask) for v in Adj[i][x] if mask>>v&1)
    @lru_cache(None)
    def local(ends,mask):
        if not ends:return True
        i,x,y=ends[0]; q=mask
        while q:
            if occ(i,x,y,q) and local(ends[1:],mask^q):return True
            q=(q-1)&mask
        return False
    layers={tuple(s for s,t in ST)}
    for j,C in enumerate(leaf):
        update=set()
        for x in layers:
            I=[i for i,v in enumerate(x) if v in C]
            choices=[[(ST[i][1],-1)] if ST[i][1] in C else [(y,z) for y in C for z in Adj[i][y] if z not in C] for i in I]
            for P in product(*choices):
                z=list(x); E=[]
                for i,(y,out) in zip(I,P):z[i]=out; E.append((i,x[i],y))
                if len(set(u for u in z if u!=-1))!=sum(u!=-1 for u in z):continue
                counters[1]+=1
                counters[2]+=sum(x0==y for i,x0,y in E)
                counters[3]+=sum(u>=0 and ci[u]>j+1 for u in z)
                if local(tuple(E),sum(1<<u for u in C)): update.add(tuple(z))
        layers=update
    possible=(-1,)*k in layers
    def paths(i,x):
        if x==ST[i][1]: return [1<<x]
        return [(1<<x)|p for v in Adj[i][x] for p in paths(i,v)]
    expect=False
    for P in product(*(paths(i,s) for i,(s,t) in enumerate(ST))):
        if all(not (u&v) for i,u in enumerate(P) for v in P[i+1:]):
            expect=True;break
    assert possible==expect
    counters[0]+=1
    return possible

rng=Random(17)
for _ in range(440):
    n=9;k=3
    A=[(u,v,rng.randint(1,5)) for u in range(n) for v in range(n) if u!=v and rng.randrange(3)==0]
    ST=[(i,k+i) for i in range(k)]
    if rng.randrange(6)==0: ST[1]=(1,1)
    both(n,A,ST)
for k in range(2,11):
    n=2*k; A=[(i,k+i,3) for i in range(k)]
    for i in range(k):
        for j in range(i+1,k):
            u,v=n,n+1;n+=2
            A += [(i,u,1),(u,v,1),(v,k+i,1),(j,v,1),(v,u,1),(u,k+j,1)]
    assert both(n,A,[(i,i+k) for i in range(k)],False)==2
print('exact verified instances/transitions/singleton fragments/skipped-component pending entries:',*counters)
