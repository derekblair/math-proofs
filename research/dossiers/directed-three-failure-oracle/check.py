from itertools import combinations, product
from random import Random

def ap(d):
    n=len(d)
    for k in range(n):
        for i in range(n):
            if d[i][k] is not None:
                for j in range(n):
                    if d[k][j] is not None:
                        x=tuple(a+b for a,b in zip(d[i][k],d[k][j]))
                        if d[i][j] is None or x<d[i][j]:d[i][j]=x
    return d

def shortcuts(E,n,X,f):
    d=[[None]*n for _ in range(n)]
    for i in range(n):d[i][i]=(0,0)
    for (u,v),w in E.items():d[u][v]=(w,0)
    for k in range(n):
        if k in X:continue
        for i in range(n):
            for j in range(n):
                if d[i][k] is not None and d[k][j] is not None:
                    t=(d[i][k][0]+d[k][j][0],0)
                    if d[i][j] is None or t<d[i][j]:d[i][j]=t
    ret={}
    for u,v in product(X,repeat=2):
        options=[]
        for (a,b),w in E.items():
            if a!=u:continue
            if b in X:
                if b==v:options.append((w,(a,b)))
            elif d[b][v] is not None:options.append((w+d[b][v][0],(a,b)))
        ret[u,v]=sorted(options)[:f+1]
    return ret

def batch(L,X,Y,f):
    Z=sorted(X-Y);Y=sorted(Y); h=len(Y); m=h*2+len(Z)
    tag=sorted({t for a in L.values() for _,t in a});ix={t:i for i,t in enumerate(tag)}
    R={u:i for i,u in enumerate(Y)}; ZI={z:h*2+i for i,z in enumerate(Z)}
    width=max(0,(len(tag)-1).bit_length())
    ans={(u,v):{} for u,v in product(Y,repeat=2)}
    for t in range(min(f,width)+1):
        for B in combinations(range(width),t):
            for mask in product(range(2),repeat=t):
                d=[[None]*m for _ in range(m)]
                for i in range(m):d[i][i]=(0,0)
                for u in Y:
                    for v in X:
                        j=(R[v]+h) if v in R else ZI[v]
                        vals=[(w,ix[t]) for w,t in L[u,v] if all(ix[t]>>b&1==z for b,z in zip(B,mask))]
                        if vals:d[R[u]][j]=min(vals)
                for u in Z:
                    for v in X:
                        if not L[u,v] or u==v:continue
                        j=(R[v]+h) if v in R else ZI[v]
                        d[ZI[u]][j]=(L[u,v][0][0],0)
                ap(d)
                for u,v in product(Y,repeat=2):
                    out=d[R[u]][R[v]+h]
                    if out is not None:
                        w,idx=out;etag=tag[idx]
                        D=ans[u,v];D[etag]=min(D.get(etag,w),w)
    return {uv:sorted((w,t) for t,w in D.items())[:f+1] for uv,D in ans.items()}

rng=Random(1560); cases=entries=0
for z in range(400):
    n=rng.randrange(2,9); V=set(range(n)); phi=[rng.randrange(-6,7) for _ in V]
    E={(u,v):rng.randrange(5)+phi[v]-phi[u] for u,v in product(V,repeat=2) if u!=v and rng.random()<.42}
    X=set(rng.sample(sorted(V),rng.randrange(1,n+1)))
    Y=set(rng.sample(sorted(X),rng.randrange(1,len(X)+1)))
    for f in (1,2,3):
        L=shortcuts(E,n,X,f)
        assert batch(L,X,Y,f)==shortcuts(E,n,Y,f)
        cases+=1;entries+=len(Y)**2
print(cases,'negative/zero-safe batches;',entries,'ordered shortcut lists checked')
