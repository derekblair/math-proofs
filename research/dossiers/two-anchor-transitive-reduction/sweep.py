from random import Random
from itertools import product
def adj(n,E,rev=False):
    A=[[] for _ in range(n)]
    for u,v in E:
        if rev:u,v=v,u
        A[u].append(v)
    return A

def visited(A,s):
    q=[s]; S={s}
    for u in q:
        for v in A[u]:
            if v not in S:q.append(v);S.add(v)
    return S

def strong(n,E):
    return all(len(visited(adj(n,E,r),0))==n for r in (0,1))

def topo(A):
    d=[0]*len(A)
    for vs in A:
        for v in vs:d[v]+=1
    q=[u for u,x in enumerate(d) if x==0]
    for u in q:
        for v in A[u]:
            d[v]-=1
            if not d[v]:q.append(v)
    return q

def solve(n,E,F,verify=True):
    E=sorted(x for x in E if x[0]!=x[1]);k=len(F)
    assert n>1 and k
    idx={a:i for i,a in enumerate(F)}
    # Original anchor IDs are source copies; the appended IDs are sink copies.
    D=[(u, n+idx[v] if v in idx else v) for u,v in E]
    N=n+k
    outward=[[] for _ in range(N)];inward=[[] for _ in range(N)]
    od=[0]*n;ind=[0]*n
    for j,((x,y),(u,v)) in enumerate(zip(E,D)):
        outward[u].append(j);inward[v].append(j);od[x]+=1;ind[y]+=1
    internal=[u for u in topo(adj(N,D)) if u not in idx and u<n]
    assert len(internal)==n-k
    order=F+internal+list(range(n,N));pos={v:i for i,v in enumerate(order)}
    assert all(pos[u]<pos[v] for u,v in D)
    L=[set() for _ in range(N)];R=[set() for _ in range(N)]
    for i in range(k):R[n+i].add(i)
    for u in reversed(order):
        for e in outward[u]:R[u].update(R[D[e][1]])
    C=[[0]*k for _ in range(k)]; alive=[True]*len(E); checks=0; trials=0
    def delta(e,sign):
        u,v=D[e]
        for i,j in product(L[u],R[v]):
            C[i][j]+=sign
            assert C[i][j]>=0
    def check(prefix):
        nonlocal checks
        T=[(u,v) for i,(u,v) in enumerate(D) if alive[i]]
        allA=adj(N,T); exact=[visited(allA,a) for a in F]
        B=[[0]*k for _ in F]
        for u,v in T:
            if u in prefix and v not in prefix:
                # Independently use actual snapshot reaches, not maintained tags.
                lv=[i for i in range(k) if u in exact[i]]
                rv=[j for j in range(k) if n+j in visited(allA,v)]
                for i,j in product(lv,rv):B[i][j]+=1
        assert B==C
        assert all((C[i][j]>0)==(n+j in exact[i]) for i,j in product(range(k),repeat=2))
        checks+=1
    def crossing_advance(u):
        if u in idx:L[u].add(idx[u])
        for e in inward[u]:
            if alive[e]:
                delta(e,-1)
                L[u].update(L[D[e][0]])
        for e in outward[u]:delta(e,1)
    # Initialize after ALL source copies. They have no incoming edges.
    prefix=set(F)
    for u in F:crossing_advance(u)
    if verify:check(prefix)
    def try_tail(u):
        nonlocal trials
        for e in outward[u]:
            x,y=E[e]
            if od[x]==1 or ind[y]==1:continue
            delta(e,-1)
            A=[[j for j in range(k) if C[i][j]] for i in range(k)]
            B=[[i for i in range(k) if C[i][j]] for j in range(k)]
            if len(visited(A,0))==k and len(visited(B,0))==k:
                alive[e]=False;od[x]-=1;ind[y]-=1
            else:delta(e,1)
            trials+=1
            if verify:check(prefix)
    for u in F:try_tail(u)
    for u in internal:
        crossing_advance(u);prefix.add(u)
        if verify:check(prefix)
        try_tail(u)
    return {e for i,e in enumerate(E) if alive[i]},checks,trials

def run():
    rng=Random(104105); tested=checks=probes=0
    for n in range(2,5):
      for k in range(1,n+1):
        F=list(range(k));cand=[(u,v) for u in range(n) for v in range(n) if u!=v and (u<k or v<k or u<v)]
        for s in range(1<<len(cand)):
            E={e for i,e in enumerate(cand) if s>>i&1}
            if not strong(n,E):continue
            H,c,p=solve(n,E,F)
            assert strong(n,H) and H<=E and not any(strong(n,H-{e}) for e in H)
            tested+=1;checks+=c;probes+=p
    for n in range(5,22):
      for _ in range(100):
        k=rng.randrange(1,n+1); T=list(range(n));rng.shuffle(T)
        F=T[:k];X=T[k:];ordered={a:i for i,a in enumerate(X)};F0=set(F)
        E={(u,v) for u,v in product(T,repeat=2) if u!=v and (u in F0 or v in F0 or ordered[u]<ordered[v]) and rng.random()<.22}
        cycle=[F[0]]+X+F[1:]+[F[0]]
        E.update(zip(cycle,cycle[1:]))
        H,c,p=solve(n,E,F)
        assert strong(n,H) and H<=E and not any(strong(n,H-{e}) for e in H)
        tested+=1;checks+=c;probes+=p
    print(tested,'complete reductions;',checks,'independent cut count scans;',probes,'tentative deletions')
if __name__=='__main__':run()
