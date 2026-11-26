from check import ap,batch
from itertools import product
from random import Random

rng=Random(4472)
counts=[0]*5
for rep in range(220):
    n=8;V=set(range(n));st=rng.sample(sorted(V),2);s,t=st
    b=rng.choice((1,2,4,8));phi=[rng.randrange(-7,8) for _ in V]
    E={(u,v):rng.randrange(5)+phi[v]-phi[u] for u,v in product(V,repeat=2) if u!=v and rng.random()<.48}
    def APSP(edges,ve):
        M=[[None]*ve for _ in range(ve)]
        for i in range(ve):M[i][i]=(0,0)
        for (u,v),w in edges.items():M[u][v]=(w,1)
        return ap(M)
    pot=[z[0] for z in APSP(E|{(n,v):0 for v in V},n+1)[n][:n]]
    cache={}; d=0
    for _ in range(28):
        F=set(rng.sample(tuple(E),rng.randint(0,min(3,len(E)))))
        idx=tuple(sorted(set(u//b for u,v in F))) or (s//b,)
        if idx not in cache:
            X=V
            P={(u,v):[(E[u,v],(u,v))] if (u,v) in E else [] for u,v in product(V,repeat=2)}
            size=n
            while size>b:
                size//=2
                Y=set(st)|{v for v in X if any(v//size==i*b//size for i in idx)}
                P=batch(P,X,Y,3);X=Y
            cache[idx]=(X,P)
        X,P=cache[idx]
        assert set(st)|{u for u,v in F}<=X
        M={u:{} for u in X}
        for (u,v),L in P.items():
            vals=[w+pot[u]-pot[v] for w,e in L if e not in F]
            assert min(vals,default=0)>=0
            if vals:M[u][v]=min(vals)
        label={s:0};rem=set(X)
        while rem:
            opts=rem&label.keys()
            if not opts:break
            u=min(opts,key=label.get);rem.remove(u)
            if u==t:break
            for v,w in M[u].items():
                if v in rem:
                    cand=label[u]+w
                    if v not in label or cand<label[v]:label[v]=cand
        ans=None if t not in label else label[t]-pot[s]+pot[t]
        raw=APSP({e:w for e,w in E.items() if e not in F},n)[s][t]
        assert ans==(None if raw is None else raw[0])
        counts[0]+=1;counts[1]+=not F
        counts[2]+=len(F)!=len({u for u,v in F})
        counts[3]+=ans is None;counts[4]+=ans is not None and ans<0
print('stopped queries / no failures / repeated tails / unreachable / negative distance:',*counts)
