from itertools import product
from random import Random

def prune(S):
    W={}
    for w,e in S:W[e]=min(w,W.get(e,w))
    return sorted((w,e) for e,w in W.items())[:4]

def eliminate(P,X,Y):
    X=set(X);T=dict(P)
    for z in sorted(X-Y):
        X.remove(z)
        M={}
        for u,v in product(X,repeat=2):
            c=T[z,v]
            M[u,v]=prune(T[u,v]+([(w+c[0][0],e) for w,e in T[u,z]] if c else []))
        T=M
    return T

def query(P,X,s,t,F,p):
    D={s:0};S=set(X)
    while S:
        live=S&D.keys()
        if not live:break
        u=min(live,key=D.get);S.remove(u)
        if u==t:return D[t]+p[t]-p[s]
        for v in S:
            for w,e in P[u,v]:
                if e not in F:
                    w+=p[u]-p[v]
                    assert w>=0
                    if D[u]+w<D.get(v,float('inf')):D[v]=D[u]+w
                    break
    return None

def batch(P,V,s,t,queries,p,beta):
    roots={s,t};out={};moves=[0]*4
    def macro(P,V,ids):
        V=sorted(V);d=1<<(len(V)-1).bit_length(); rank={v:i for i,v in enumerate(V)}
        def go(P,X,ids,k):
            R=roots|{a for i in ids for a,b in queries[i]}
            r=len(R)
            if k==1:
                for i in ids:out[i]=query(P,X,s,t,queries[i],p)
                moves[0]+=1;return
            # The operational test compares a conservative head count here;
            # toy beta intentionally exercises paths at small sizes.
            if r<len(X) and r<=beta*k:
                Z=eliminate(P,X,R)
                if len(ids)*r*r<=k*k and len(ids)%2:
                    for i in ids:out[i]=query(Z,R,s,t,queries[i],p)
                    moves[1]+=1
                else:
                    moves[2]+=1
                    macro(Z,R,ids)
                return
            groups={}
            for i in ids:
                needs=sorted({rank[a] for a,b in queries[i]}) or [rank[s]]
                addr=tuple([*needs,*([needs[-1]]*(3-len(needs)))])
                ju=tuple(a//(k//2) for a in addr)
                groups.setdefault(ju,[]).append(i)
            for jc,I in groups.items():
                Y=roots|{u for u in X if rank[u]//(k//2) in jc}
                assert all(roots|{a for a,b in queries[i]}<=Y for i in I)
                go(eliminate(P,X,Y),Y,I,k//2);moves[3]+=1
        go(P,set(V),ids,d)
    macro(P,V,list(range(len(queries))))
    assert len(out)==len(queries)
    return [out[i] for i in range(len(queries))],moves

rng=Random(51254);counts=[0]*10
for rep in range(350):
    n=rng.randint(4,18);V=set(range(n));s,t=rng.sample(sorted(V),2)
    ps=[rng.randint(-12,12) for _ in V]
    E={(u,v):rng.randrange(5)+ps[v]-ps[u] for u,v in product(V,repeat=2) if u!=v and rng.random()<.55}
    P={(u,v):[(E[u,v],(u,v))] if (u,v) in E else [] for u,v in product(V,repeat=2)}
    R=set(rng.sample(sorted(V),rng.randint(1,n))) if rep%2 else set(rng.sample(sorted(V),2))
    fa=[e for e in E if e[0] in R]
    Q=[set(rng.sample(fa,rng.randint(0,min(3,len(fa))))) for i in range(rng.randint(1,40))]
    ans,stat=batch(P,V,s,t,Q,ps,.53)
    for F,a in zip(Q,ans):
        d={s:0}
        for _ in range(n-1):
            for (u,v),w in E.items():
                if u in d and (u,v) not in F:
                    nw=d[u]+w
                    if v not in d or nw<d[v]:d[v]=nw
        assert a==d.get(t)
        counts[0]+=1;counts[1]+=a is None;counts[2]+=a is not None and a<0
        counts[3]+=len(F)!=len({u for u,v in F});counts[4]+=not F;counts[5]+=any(s in e or t in e for e in F)
    for i,m in enumerate(stat,6):counts[i]+=m
print('queries / unreachable / negative / repeated tails / no failures / terminal fault / leaf / direct trim / restart / trie split:',*counts)
