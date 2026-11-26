from check import ap
from itertools import product,combinations
from random import Random

def masks(T,f):
    return [(a,b) for r in range(min(f,max(0,(T-1).bit_length()))+1)
            for a in combinations(range(max(0,(T-1).bit_length())),r)
            for b in product(range(2),repeat=r)]
def batch(P,X,Y,f):
    x={v:i for i,v in enumerate(sorted(X))};z=X-Y
    si={v:i+len(x) for i,v in enumerate(sorted(Y))}
    ds=set(Y);sz=len(x)+len(Y)
    tags=sorted({e for L in P.values() for w,h,e,path in L});rank={e:i for i,e in enumerate(tags)}
    def first(U,where,one):
        D=[[None]*sz for _ in range(sz)]
        for i in range(sz):D[i][i]=(0,0,0,0)
        for u,v in product(z,X):
            if u!=v and P[u,v]:
                a=P[u,v][0]
                D[x[u]][x[v]]=(a[0],a[1],0,0)
        for u,v in product(U,X):
            if where(u,v):
                b=one(u,v)
                if b is not None:D[si[u]][x[v]]=b
        return ap(D)
    # Test oracle with one duplicate source for each X vertex, reused between phases.
    si={v:i+len(x) for i,v in enumerate(sorted(X))};sz=2*len(X)
    def sl(u,v):
        if P[u,v]:
            w,h,tag,path=P[u,v][0]
            return w,h,0,x[v]
    suf=first(z,lambda u,v:u!=v,sl)
    ans={(u,v):{} for u,v in product(Y,repeat=2)}
    for B,M in masks(len(tags),f):
        def ml(u,v):
            a=next(((w,h,rank[t],x[v]) for w,h,t,_ in P[u,v] if all(rank[t]>>i&1==b for i,b in zip(B,M))),None)
            return a
        D=first(Y,lambda u,v:True,ml)
        Xlist=sorted(X)
        for u,v in product(Y,repeat=2):
            if D[si[u]][x[v]] is None:continue
            w,h,t,mid=D[si[u]][x[v]]
            mid=Xlist[mid];tag=tags[t]
            p=list(next(path for _,_,et,path in P[u,mid] if et==tag))
            hleft=h-len(p)
            while mid in z:
                ww,hh,_,i2=suf[si[mid]][x[v]]
                assert hh==hleft
                nex=Xlist[i2]
                q=P[mid,nex][0][3]
                p.extend(q)
                hleft-=len(q);mid=nex
            assert mid==v and len(p)==h and hleft==0
            old=ans[u,v].get(tag)
            new=w,h,tag,tuple(p)
            if old is None or new<old:ans[u,v][tag]=new
    return {uv:sorted(D.values())[:f+1] for uv,D in ans.items()}

rng=Random(4522)
queries=repeat=unreachable=zeros=0
for gen in range(350):
    n=rng.randint(3,9);V=set(range(n));phi=[rng.randrange(-4,5) for i in V]
    E={(u,v):rng.randrange(4)+phi[v]-phi[u] for u,v in product(V,repeat=2) if u!=v and rng.random()<.52}
    X=set(rng.sample(sorted(V),rng.randint(2,n))); Y=set(rng.sample(sorted(X),rng.randint(2,len(X))))
    P={(u,v):[(E[u,v],1,(u,v),((u,v),))] if (u,v) in E else [] for u,v in product(V,repeat=2)}
    YP=batch(batch(P,V,X,3),X,Y,3)
    use=[a for a in E if a[0] in Y]
    for q in range(28):
        F=set(rng.sample(use,rng.randint(0,min(3,len(use)))))
        repeat+=int(len({a[0] for a in F})!=len(F))
        u,v=rng.sample(sorted(Y),2)
        def mm(graph,vertices):
            idx={v:i for i,v in enumerate(sorted(vertices))}
            D=[[None]*len(vertices) for _ in vertices]
            for i in range(len(D)):D[i][i]=(0,0)
            for (a,b),w in graph.items():
                if a!=b:D[idx[a]][idx[b]]=w
            return ap(D)[idx[u]][idx[v]]
        direct=mm({a:(w,1) for a,w in E.items() if a not in F},V)
        Q={}
        for (a,b),L in YP.items():
            t=next(((w,h,path) for w,h,e,path in L if e not in F),None)
            if t is not None:Q[a,b]=t
        assert mm({a:t[:2] for a,t in Q.items()},Y)==direct
        if direct is None:unreachable+=1
        else:
            zeros+=int(direct[0]==0)
            t=u;full=[];L=direct
            while t!=v:
                for r in Y:
                    if (t,r) not in Q or r==t:continue
                    a,b,path=Q[t,r]
                    if r==v: suf=(0,0)
                    else:
                        old=u;u=r;suf=mm({a:t[:2] for a,t in Q.items()},Y);u=old
                    if suf is not None and (a+suf[0],b+suf[1])==L:
                        t=r;L=suf;full.extend(path);break
                else:raise AssertionError("missing witness")
            assert len(full)==direct[1] and len({u,*[b for _,b in full]})==len(full)+1 and len(full)<n
            assert not F&set(full) and sum(E[a] for a in full)==direct[0]
            assert full[0][0]==u and full[-1][1]==v and all(a[1]==b[0] for a,b in zip(full,full[1:]))
        queries+=1
print(queries,'distance/path queries;',repeat,'repeated-tail failures;',unreachable,'unreachable;',zeros,'zero-distance witnesses')
