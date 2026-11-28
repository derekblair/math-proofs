from itertools import product
from functools import lru_cache
from random import Random
from operator import xor
from functools import reduce
from fractions import Fraction

def mul(a,b):
    z=0
    while b:
        if b&1:z^=a
        b>>=1;a<<=1
        if a&16:a^=19
    return z

MUL=[[mul(a,b) for b in range(16)] for a in range(16)]
def times(it):
    a=1
    for x in it:a=MUL[a][x]
    return a
def plus(it):return reduce(xor,it,0)
def pathsums(N,E):
    A=[[] for _ in range(N)]
    for (u,v),x in E.items():A[u].append((v,x))
    def propagate(row,l=0,r=N, squared=False):
        V=row[:]
        for u in range(l,r):
            for v,x in A[u]:
                if v<r: V[v]^=MUL[V[u]][MUL[x][x] if squared else x]
        return V
    T=[propagate([int(v==u) for v in range(N)],u) for u in range(N)]
    return T,propagate
def arc_masks(n,W,S,shortest):
    if not shortest:return [set(W) for _ in S]
    H=[]
    for s in S:
        d=[None]*n;d[s]=Fraction(0)
        for a in range(n):
            if d[a] is None:continue
            for b in range(a+1,n):
                if (a,b) in W:
                    q=d[a]+W[a,b]
                    if d[b] is None or q<d[b]:d[b]=q
        H.append({(a,b) for (a,b),w in W.items() if d[a] is not None and d[a]+w==d[b]})
    return H

def verify(n,k,X,H,ST,check_generic=True):
    # Same base variable per arc; private normalization arc values 1.
    lo=k;hi=k+n;N=hi+k
    X0=[{(u+k,v+k):X[u,v] for u,v in H[i]} for i in range(k)]
    E=[A | {(i,s+k):1,(t+k,hi+i):1} for i,(A,(s,t)) in enumerate(zip(X0,ST))]
    data=[pathsums(N,A) for A in E]
    A=[v[0] for v in data]
    K={}
    for i in range(k):
        for j in range(i+1,k):
            Z={e:x for e,x in X0[i].items() if e in X0[j]}
            T,prop=pathsums(N,Z);K[i,j]=prop
            for u in range(lo,hi):
                for v in range(u+1,hi):
                    assert MUL[A[i][u][v]][A[j][u][v]]==MUL[T[u][v]][T[u][v]]
    events=[tuple(i for i in range(k) if b>>i&1) for b in range(1<<k) if b.bit_count()>=2]
    outside={S:tuple(i for i in range(k) if i not in S) for S in events}
    def endpoint(S,w,c):
        e=[w]*k
        for i,u in zip(outside[S],c):e[i]=u
        return e
    def independent(e):return times(A[i][i][u] for i,u in enumerate(e))
    acc={(S,v,c):0 for v in range(lo,hi) for S in events for c in product(range(v),repeat=len(outside[S]))}
    rows={}
    nstate=0
    def extend(T,w,end):
        r=len(outside[T]);D=rows[T,w]
        for p,i in enumerate(outside[T]):
            C={}
            def ins(b,c):return b[:p]+(c,)+b[p:]
            for other in product(range(end),repeat=r-1):
                vec=[0]*N
                for (u,v),x in E[i].items():
                    if u<w<v<end:vec[v]^=MUL[D.get(ins(other,u),0)][x]
                V=data[i][1](vec,w+1,end)
                for e in range(end):
                    C[ins(other,e)]=D.get(ins(other,e),0) if e<w else 0 if e==w else V[e]
            D=C
        return D
    def contribution(Y,T,w,e):
        return times([Y[T,w][tuple(e[i] for i in outside[T])]]+[A[i][w][e[i]] for i in T])
    def solve(a,b):
        nonlocal nstate
        if a+1==b:
            w=a
            for T in events:
                rows[T,w]={c:independent(endpoint(T,w,c))^acc[T,w,c] for c in product(range(w),repeat=len(outside[T]))}
            return
        med=(a+b)//2;solve(a,med)
        W=range(a,med);V=range(med,b)
        Y={(T,w):extend(T,w,b) for T in events for w in W}
        D={(S,v,c):0 for S in events for v in V for c in product(range(v),repeat=len(outside[S]))}
        for S in events:
            if len(S)>2:
                for key in D:
                    if key[0]!=S:continue
                    _,v,c=key;e=endpoint(S,v,c)
                    D[key]=plus(contribution(Y,T,w,e) for T in events for w in W)
                continue
            for T in events:
                if T==S:
                    for c in product(range(b),repeat=k-2):
                        P=[0]*N
                        for w in W:P[w]=Y[S,w][c]
                        Z=K[S](P,a,b,True)
                        for v in V:
                            if all(z<v for z in c):D[S,v,c]^=Z[v]
                else:
                    j=next(i for i in T if i not in S); position=outside[S].index(j)
                    def ins(other,e):return other[:position]+(e,)+other[position:]
                    for v in V:
                        for other in product(range(v),repeat=k-3):
                            e=endpoint(S,v,ins(other,0));P=[0]*N
                            for w in W:
                                P[w]=times([Y[T,w][tuple(e[i] for i in outside[T])]]+[A[i][w][e[i]] for i in T if i!=j])
                            Z=data[j][1](P)
                            for cj in range(v):D[S,v,ins(other,cj)]^=Z[cj]
        if check_generic:
            for (S,v,c),q in D.items():
                e=endpoint(S,v,c)
                assert q==plus(contribution(Y,T,w,e) for T in events for w in W)
                nstate+=1
        for key,val in D.items():acc[key]^=val
        solve(med,b)
    solve(lo,hi)
    Y={(T,w):extend(T,w,N) for T in events for w in range(lo,hi)}
    e=list(range(hi,N))
    result=independent(e)^plus(contribution(Y,T,w,e) for T in events for w in range(lo,hi))
    @lru_cache(None)
    def paths(i,u):
        if u==ST[i][1]:return [(1<<u,1,frozenset())]
        return [(a|(1<<u),MUL[y][X[v,z]],m|{(v,z)}) for v,z in H[i] if v==u for a,y,m in paths(i,z)]
    allpaths=[paths(i,s) for i,(s,t) in enumerate(ST)]
    monomials=set()
    expect=0
    def brute(i,used,coefficient,edges):
        nonlocal expect
        if i==k:
            assert edges not in monomials
            monomials.add(edges);expect^=coefficient
            return
        for a,y,m in allpaths[i]:
            if not a&used:brute(i+1,used|a,MUL[y][coefficient],edges|m)
    brute(0,0,1,frozenset())
    assert result==expect
    return nstate,len(monomials),bool(result)

rng=Random(37);checks=0;scatters=0;monomials=0;nonzero=0
for k in (3,4):
    for _ in range(24):
        n=2*k+rng.randrange(3)
        S=list(range(k));ST0=list(zip(S,range(n-k,n)))
        W={(u,v):Fraction(rng.randrange(-5,6),rng.randrange(1,6)) for u in range(n) for v in range(u+1,n) if rng.randrange(3)==0 or (u,v) in ST0}
        X={e:rng.randrange(16) for e in W}
        H=arc_masks(n,W,S,bool(_%2))
        R=sorted(rng.sample(range(n),n-1)) if _%4==0 else list(range(n))
        Tmap={v:u for u,v in enumerate(R)}; LX={(Tmap[u],Tmap[v]):x for (u,v),x in X.items() if u in Tmap and v in Tmap}
        L=[{(Tmap[u],Tmap[v]) for u,v in M if u in Tmap and v in Tmap} for M in H]
        ST=ST0
        if _%4==0:
            # Child changes real terminals and one inactive label becomes an isolated dummy.
            endpoints=sorted(rng.sample(R,2*(k-1)))
            ST=list(zip(endpoints[:k-1],endpoints[k-1:]))+[(n,n)]
            Tmap[n]=len(R);L[-1]=set()
        D=verify(len(Tmap),k,LX,L,[(Tmap[s],Tmap[t]) for s,t in ST])
        checks+=1;scatters+=D[0];monomials+=D[1];nonzero+=D[2]
print(checks,'complete GF(16) circuits;',scatters,'per-entry transfer controls;',
      monomials,'unique shared-variable witness monomials;',nonzero,'nonzero evaluations')
