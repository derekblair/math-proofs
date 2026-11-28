from random import Random
from itertools import permutations

INF=10**8

def matrix(n,A):
    D=[[INF]*n for _ in range(n)]
    for i in range(n): D[i][i]=0
    for i,j,w in A: D[i][j]=min(D[i][j],w)
    for q in range(n):
        for i in range(n):
            for j in range(n):
                if D[i][q]<INF and D[q][j]<INF:
                    D[i][j]=min(D[i][j],D[i][q]+D[q][j])
    return D

def verify(n,k,A):
    D=matrix(n,A); I=range(k)
    start=lambda i:i
    target=lambda i:k+i
    C=lambda D,i,j:D[start(i)][target(j)]
    if any(C(D,i,i)==INF for i in I):return 0,None
    E=[{(u,v,w) for u,v,w in A if D[start(i)][u]+w+D[v][target(i)]==C(D,i,i)} for i in I]
    U=set().union(*E)
    F=matrix(n,U)
    assert all(C(F,i,i)==C(D,i,i) for i in I)
    bymask=[True]
    for mask in range(1,1<<k):
        G=[i for i in I if mask>>i&1]
        base=sum(C(F,i,i) for i in G)
        opt=min(sum(C(F,i,j) for i,j in zip(G,P)) for P in permutations(G))
        La=[(i,j,C(F,i,j)-C(F,j,j)) for i in G for j in G if C(F,i,j)<INF]
        V=matrix(k,La)
        T=matrix(n,U|{(target(i),start(i),-C(F,i,i)) for i in G})
        R=matrix(n,U|{(v,u,-w) for i in G for (u,v,w) in E[i]})
        pred=opt==base
        assert pred==all(V[i][i]>=0 for i in G)==all(T[i][i]>=0 for i in range(n))==all(R[i][i]>=0 for i in range(n))
        if pred:
            # Distances from a new zero-weight source to all original vertices.
            phi=[min(T[u][v] for u in range(n)) for v in range(n)]
            assert all(phi[v]-phi[u]<=w for u,v,w in U)
            assert all(phi[v]-phi[u]==w for i in G for u,v,w in E[i])
        bymask.append(pred)
    best=[0]
    for mask in range(1,1<<k):
        b=k; q=mask
        while q:
            if bymask[q]: b=min(b,1+best[mask^q])
            q=(q-1)&mask
        best.append(b)
    return (1<<k)-1,best[-1]

rng=Random(4); cases=0
for _ in range(130):
    k=3; n=10
    A=[(u,v,rng.randint(1,10)) for u in range(n) for v in range(n) if u!=v and rng.randrange(4)==0]
    cnt,_=verify(n,k,A); cases+=cnt
for k in range(2,7):
    for label in ('empty','bipartite','complete'):
        A=[(i,k+i,3) for i in range(k)]; n=2*k
        for i in range(k):
            for j in range(i+1,k):
                if label=='empty' or (label=='bipartite' and i%2==j%2):continue
                u,v=n,n+1;n+=2
                A +=[(i,u,1),(u,v,1),(v,k+i,1),(j,v,1),(v,u,1),(u,k+j,1)]
        cnt,b=verify(n,k,A); cases+=cnt
        assert b=={'empty':1,'bipartite':2,'complete':k}[label]
print(cases,'exact subset equivalence and feasible-potential checks')
