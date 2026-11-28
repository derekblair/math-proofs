from functools import lru_cache
from itertools import product
from math import prod
from random import Random

P=101
comm=lambda q: tuple(i for i in range(q.bit_length()) if q>>i&1)
def mm(A,B):
    return [[sum(u*v for u,v in zip(a,col))%P for col in zip(*B)] for a in A]

def fixture(k,n,rng):
    M=2*k+n; lo=k; hi=k+n
    I=[comm(b) for b in range(1<<k) if b.bit_count()>=2]
    O={T:tuple(i for i in range(k) if i not in T) for T in I}
    X=[[[0]*M for _ in range(M)] for _ in range(k)]
    for i in range(k):
        X[i][i][lo+(i if i<n else 0)]=1
        X[i][hi-1-i%n][hi+i]=1
        for u in range(lo,hi):
            for v in range(u+1,hi):
                if rng.randrange(3)!=0: X[i][u][v]=rng.randrange(1,P)
    N=[]
    for W in X:
        D=[[0]*M for _ in range(M)]
        for u in reversed(range(M)):
            D[u][u]=1
            for v,x in enumerate(W[u]):
                if x:
                    for t in range(v,M):D[u][t]=(D[u][t]+x*D[v][t])%P
        N.append(D)

    def ep(T,w,c):
        E=[w]*k
        for i,a in zip(O[T],c): E[i]=a
        return E
    def base(E):return prod(N[i][i][e] for i,e in enumerate(E))%P
    def standard(T,w,A,limit):
        D=dict(A); r=len(O[T])
        for j,i in enumerate(O[T]):
            K=[[((1 if z==e else 0) if e<w else 0 if e==w else sum(X[i][z][d]*N[i][d][e] for d in range(w+1,e+1)))%P for e in range(limit)] for z in range(w)]
            nxt={}
            for a in product(range(limit),repeat=r):
                nxt[a]=sum(D.get(a[:j]+(z,)+a[j+1:],0)*K[z][a[j]] for z in range(w))%P
            D=nxt
        return D

    def cohort(T,W,A,left,right):
        r=len(O[T]);D={w:dict(A[T,w]) for w in W}
        for j,i in enumerate(O[T]):
            rows=[(w,c) for w in W for c in product(range(right),repeat=r-1)]
            def insert(c,a):return c[:j]+(a,)+c[j:]
            V=[[D[w].get(insert(c,a),0) if a<w else 0 for a in range(right)] for w,c in rows]
            L=mm(V,[X[i][a][left:right] for a in range(right)])
            for (w,c),row in zip(rows,L):
                for d in range(left,min(w+1,right)):row[d-left]=0
            B=mm(L,[N[i][a][left:right] for a in range(left,right)])
            Y={w:{} for w in W}
            for (w,c),row in zip(rows,B):
                for a in range(right):
                    e=insert(c,a)
                    Y[w][e]=D[w].get(e,0) if a<w else 0 if a==w else row[a-left]
            D=Y
        return D
    def B_at(E,w,batch):
        return sum(batch[T][w].get(tuple(E[i] for i in O[T]),0)*prod(N[i][w][E[i]] for i in T) for T in I)%P

    rows={}
    acc={(S,v,c):0 for S in I for v in range(lo,hi) for c in product(range(v),repeat=len(O[S]))}
    ops=[0,0]
    def solve(l,r):
        if l+1==r:
            for S in I:
                rows[S,l]={c:(base(ep(S,l,c))-acc[S,l,c])%P for c in product(range(l),repeat=len(O[S]))}
            return
        mid=(l+r)//2;solve(l,mid);W=range(l,mid);V=range(mid,r)
        Y={T:cohort(T,W,rows,l,r) for T in I}
        for T in I:
            for w in W:
                # All available tensor entries, not just accesses observed below.
                exact=standard(T,w,rows[T,w],r)
                assert all(exact[e]==Y[T][w].get(e,0) for e in exact)
                ops[0]+=len(exact)
        old={(S,v,c):sum(B_at(ep(S,v,c),w,Y) for w in W)%P for S in I for v in V for c in product(range(v),repeat=len(O[S]))}
        new=dict.fromkeys(old,0)
        for S in I:
            if len(S)>2:
                for key,value in old.items():
                    if key[0]==S:new[key]=value
                continue
            for T in I:
                if T==S:
                    Q=list(product(range(r),repeat=len(O[S])))
                    Z=mm([[prod(N[i][w][v] for i in T)%P for w in W] for v in V],
                         [[Y[T][w].get(c,0) for c in Q] for w in W])
                    for v,z in zip(V,Z):
                        for c,value in zip(Q,z):
                            if (S,v,c) in new:new[S,v,c]=(new[S,v,c]+value)%P
                else:
                    j=next(i for i in T if i not in S); z=O[S].index(j)
                    F=[(v,f) for v in V for f in product(range(r),repeat=len(O[S])-1)]
                    AP=[]
                    for v,f in F:
                        E=ep(S,v,f[:z]+(0,)+f[z:])
                        AP.append([Y[T][w].get(tuple(E[i] for i in O[T]),0)*prod(N[i][w][E[i]] for i in T if i!=j)%P for w in W])
                    C=mm(AP,[N[j][w][:r] for w in W])
                    for (v,f),row in zip(F,C):
                        for cj,value in enumerate(row):
                            c=f[:z]+(cj,)+f[z:]
                            if (S,v,c) in new:new[S,v,c]=(new[S,v,c]+value)%P
        assert old==new;ops[1]+=len(new)
        for key,x in new.items():acc[key]=(acc[key]+x)%P
        solve(mid,r)
    solve(lo,hi)
    E=list(range(hi,M));Y={T:cohort(T,range(lo,hi),rows,lo,M) for T in I}
    F=(base(E)-sum(B_at(E,w,Y) for w in range(lo,hi)))%P
    @lru_cache(None)
    def paths(i,u):
        if u==hi+i:return [(0,1)]
        out=[]
        for v,x in enumerate(X[i][u]):
            if x:
                for a,b in paths(i,v):out.append((a|((1<<u) if lo<=u<hi else 0),x*b%P))
        return out
    @lru_cache(None)
    def brute(i,used):
        if i==k:return 1
        return sum(y*brute(i+1, used|a) for a,y in paths(i,i) if not a&used)%P
    expected=brute(0,0)
    assert F==expected
    return ops

rng=Random(5)
allcounts=[fixture(k,n,rng) for k,n,reps in [(4,6,6),(4,9,8),(5,6,3),(5,10,3)] for _ in range(reps)]
print('20 exact first-collision circuits against brute path tuples;',sum(s[0] for s in allcounts),'kernel entries;',sum(s[1] for s in allcounts),'scatter entries')
