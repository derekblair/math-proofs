"""Exact integer differential check of the boundary-roster DP."""
from functools import lru_cache
from itertools import permutations,product
from random import Random

INF=10**9

def init(n,edges,term):
    k=len(term); D=[[0 if i==j else INF for j in range(n)] for i in range(n)]
    for u,v,w in edges:D[u][v]=min(D[u][v],w)
    for z in range(n):
        for i in range(n):
            for j in range(n):D[i][j]=min(D[i][j],D[i][z]+D[z][j])
    if any(D[s][t]==INF for s,t in term):return None
    P=[[min(D[s][v],D[s][t]) for s,t in term] for v in range(n)]
    X=[tuple(x-p[-1] for x in p[:-1]) for p in P]
    A=[(i,u,v) for i,(s,t) in enumerate(term) for u,v,w in edges if D[s][u]+w+D[v][t]==D[s][t]]
    for i,u,v in A:
        assert all(P[v][i]-P[v][j] >= P[u][i]-P[u][j] for j in range(k))
    return P,X,A

def brute(n,term,data):
    if data is None:return False
    A=data[2]
    adv=[{} for i in term]
    for i,u,v in A:adv[i].setdefault(u,[]).append(v)
    def walk(i,u,V):
        if u==term[i][1]:yield V;return
        for v in adv[i].get(u,[]):
            assert not V>>v&1
            yield from walk(i,v,V|(1<<v))
    L=[list(walk(i,s,1<<s)) for i,(s,t) in enumerate(term)]
    def cover(i,M):
        if i==len(term):return True
        return any(not(M&p) and cover(i+1,M|p) for p in L[i])
    return cover(0,0)

def dp(n,term,data):
    if data is None:return False,0,0,0
    P,X,A=data;k=len(term);lim=18*k*(k-1)
    leaf_calls=overlap=token_calls=0
    def fragment(U,B):
        nonlocal leaf_calls,overlap,token_calls
        leaf_calls+=1
        owners={}; src=[set() for t in term];sink=[set() for t in term]
        def add(v,i,S):
            if owners.get(v,i)!=i or v in S[i]:return False
            owners[v]=i;S[i].add(v);return True
        for i,(s,t) in enumerate(term):
            if s in U and not add(s,i,src):return False
            if t in U and not add(t,i,sink):return False
        for x in B:
            i,u,v=A[x]
            if u in U and not add(u,i,sink):return False
            if v in U and not add(v,i,src):return False
        forbid=set()
        for i in range(k):
            common=src[i]&sink[i]
            forbid|=common; src[i]-=common;sink[i]-=common
            if len(src[i])!=len(sink[i]):return False
        overlap+=len(forbid)
        U=U-forbid
        allowed=[{} for i in term]
        ranking={v:h for h,v in enumerate(sorted(U,key=lambda v:(P[v][0],v)))}
        for i,u,v in A:
            if u in U and v in U:
                assert P[u][0]<P[v][0]
                allowed[i].setdefault(u,[]).append(v)
        for end in product(*(permutations(L) for L in sink)):
            opts=[(i,u,v) for i in range(k) for u,v in zip(sorted(src[i]),end[i])]
            st=tuple(u for i,u,v in opts); en=tuple(v for i,u,v in opts)
            ports=set(st)|set(en)
            @lru_cache(None)
            def go(pos):
                nonlocal token_calls
                token_calls+=1
                rem=[i for i,(p,q) in enumerate(zip(pos,en)) if p!=q]
                if not rem:return True
                q=min(rem,key=lambda i:ranking[pos[i]])
                for r in allowed[opts[q][0]].get(pos[q],[]):
                    if r in pos or (r in ports and r!=en[q]):continue
                    p=list(pos);p[q]=r
                    if go(tuple(p)):return True
                return False
            if go(st):return True
        return False
    @lru_cache(None)
    def go(U,B):
        if len({X[v] for v in U})==1:return fragment(U,B)
        splits=set()
        for j in range(k-1):
            vals=sorted({X[v][j] for v in U})
            for c in vals[:-1]:
                L=frozenset(v for v in U if X[v][j]<=c);R=U-L
                if L not in splits:
                    splits.add(L)
                    BG,BR=[],[]
                    for x in B:
                        i,u,v=A[x]
                        (BG if u in L or v in L else BR).append(x)
                    Q=[x for x,(i,u,v) in enumerate(A) if (u in L and v in R) or (u in R and v in L)]
                    for bits in range(1<<len(Q)):
                        W=[x for h,x in enumerate(Q) if bits>>h&1]
                        if max(len(BG),len(BR))+len(W)>lim:continue
                        if go(L,tuple(sorted(BG+W))) and go(R,tuple(sorted(BR+W))):return True
        return False
    ans=go(frozenset(range(n)),())
    return ans,leaf_calls,overlap,token_calls

if __name__=='__main__':
    R=Random(617)
    cases=[]
    # Explicit two ways through a tied shared corridor; edge and vertex
    # assignments with ties inside common DAG leaves, and forced singletons.
    for i in range(70):
        n=7 if i%2 else 8;k=2 if i%3 else 3
        term=[(2*j,2*j+1) for j in range(k)]
        if i%7==0:term[0]=(0,0)
        # Positive integer weights, dense cyclic and strongly tied instances.
        edges=[(u,v,R.randrange(1,2 if i%3==0 else 5)) for u in range(n) for v in range(n) if u!=v and R.randrange(10)<3+i%4]
        cases.append((n,edges,term))
    cases.append((8,[(0,4,1),(2,4,1),(4,5,1),(5,6,1),(6,1,1),(6,3,1),
                     (4,7,1),(7,6,1)],[(0,1),(2,3)]))
    cases.append((8,[(0,4,1),(2,4,1),(4,5,1),(5,6,1),(6,1,1),(6,3,1),
                     (4,7,1),(7,6,1),(0,1,4),(2,3,4)],[(0,1),(2,3)]))
    totals=[0,0,0,0]
    for n,E,T in cases:
        data=init(n,E,T)
        got=dp(n,T,data)
        assert got[0]==brute(n,T,data),(n,E,T,got)
        for i,x in enumerate(got):totals[i]+=x
    print('integer graph cases',len(cases),'yes, leaf states, forced singleton count, token states:',totals)
