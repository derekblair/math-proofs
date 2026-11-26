from itertools import combinations,product
from random import Random

def floyd(D):
    for z in range(len(D)):
        for u in range(len(D)):
            if D[u][z] is None:continue
            for v in range(len(D)):
                if D[z][v] is not None:
                    t=tuple(a+b for a,b in zip(D[u][z],D[z][v]))
                    if D[u][v] is None or t<D[u][v]:D[u][v]=t
    return D

def compress(S,f):
    S=sorted(set(S));O=set()
    def rec(B,d):
        a=next((a for a in S if (0,a[2]) not in B and (1,a[3]) not in B),None)
        if a is None:return
        O.add(a)
        if d:
            for i in (0,1):rec(B|{(i,a[2+i])},d-1)
    rec(set(),f)
    assert len(O)<=2**(f+1)-1
    return sorted(O)

def layer(P,X,Y,okL,okR,tag):
    Z=sorted(X-Y);Y=sorted(Y);h=len(Y); sz=2*h+len(Z)
    I={v:i for i,v in enumerate(Y)}; J={v:2*h+i for i,v in enumerate(Z)}
    D=[[None]*sz for _ in range(sz)]
    for i in range(sz):D[i][i]=(0,0,0,0)
    for u,v in product(X,repeat=2):
        if u in J and v in J and u==v:continue
        A,B=u in I,v in I
        cand=[(w,hops,tag[e] if A else 0,tag[g] if B else 0)
              for w,hops,e,g in P[u,v] if (not A or okL(e)) and (not B or okR(g))]
        if cand:D[I[u] if A else J[u]][I[v]+h if B else J[v]]=min(cand)
    floyd(D)
    return {(u,v):D[I[u]][I[v]+h] for u,v in product(Y,repeat=2)}

def batch(P,X,Y,f):
    ts=sorted({e for S in P.values() for _,_,a,b in S for e in (a,b)})
    tag={e:i for i,e in enumerate(ts)};width=max(0,(len(ts)-1).bit_length())
    masks=[(sum(1<<i for i in B),sum(1<<i for i,b in zip(B,bb) if b))
        for r in range(min(f,width)+1) for B in combinations(range(width),r)
        for bb in product((0,1),repeat=r)]
    O={(u,v):set() for u,v in product(Y,repeat=2)}
    for (L,la),(R,ra) in product(masks,repeat=2):
        if L.bit_count()+R.bit_count()>f:continue
        D=layer(P,X,Y,lambda e:tag[e]&L==la,lambda e:tag[e]&R==ra,tag)
        for p,r in D.items():
            if r is not None:O[p].add((*r[:2],ts[r[2]],ts[r[3]]))
    return {p:compress(S,f) for p,S in O.items()}

rng=Random(12385);checks=[0]*8
for it in range(88):
    n=rng.randint(3,6);V=set(range(n));p=[rng.randrange(-5,6) for _ in V]
    H=set(rng.sample(sorted(V),rng.randint(1,n-1)))
    E={(u,v):rng.randrange(4)+p[v]-p[u] for u,v in product(V,repeat=2)
        if u!=v and ({u,v}&H or it%2) and rng.random()<.40}
    P={(u,v):[(E[u,v],1,(u,v),(u,v))] if (u,v) in E else [] for u,v in product(V,repeat=2)}
    s,t=rng.sample(sorted(V),2)
    X=H|{s,t}; B=batch(P,V,X,3); tag={e:i for i,e in enumerate(sorted(E))}
    Y=set(rng.sample(sorted(X),rng.randint(1,len(X)))); C=batch(B,X,Y,3)
    side=[(i,e) for i in (0,1) for e in E]
    if not it%2 and n>len(X):
        tiles=[]
        for v in V-X:
            XP=X|{v}
            tiles.append(batch({p:P[p] for p in product(XP,repeat=2)},XP,X,3))
        alt={p:compress([r for tile in tiles for r in tile[p]],3) for p in B}
        for _ in range(8):
            forbid=set(rng.sample(side,rng.randint(0,min(3,len(side)))))
            def weights(L):
                return min(((w,h) for w,h,e,g in L if (0,e) not in forbid and (1,g) not in forbid),default=None)
            assert all(weights(alt[p])==weights(B[p]) for p in B)
            checks[7]+=len(B)
    for _ in range(30):
        forbid=set(rng.sample(side,rng.randint(0,min(3,len(side)))))
        a=lambda e:(0,e) not in forbid
        b=lambda e:(1,e) not in forbid
        expect=layer(P,V,Y,a,b,tag)
        for uv,L in C.items():
            vals=[(w,h,tag[e],tag[g]) for w,h,e,g in L if a(e) and b(g)]
            # Only (weight,hops) are required across the local reordering.
            real=min(vals,default=None)
            assert (None if real is None else real[:2])==(None if expect[uv] is None else expect[uv][:2])
            checks[0]+=1
        checks[1]+=sum((0,e) in forbid and (1,e) in forbid for e in E)
    for _ in range(25):
        F=set(rng.sample(list(E),rng.randint(0,min(3,len(E)))))
        # Only query sets with a chosen vertex in X incident to each failed edge.
        if any(not(set(e)&X) for e in F): continue
        FL={e for e in F if e[0] in X}; FR=F-FL
        D=[[None]*n for _ in V]; M=[[None]*len(X) for _ in X];XX={v:i for i,v in enumerate(sorted(X))}
        for i in V:D[i][i]=(0,0)
        for i in XX.values():M[i][i]=(0,0)
        for (u,v),w in E.items():
            if (u,v) not in F:D[u][v]=(w,1)
        for (u,v),L in B.items():
            vals=[(w,h) for w,h,e,g in L if e not in FL and g not in FR]
            if vals and u!=v:M[XX[u]][XX[v]]=min(vals)
        A=floyd(D)[s][t]; Q=floyd(M)[XX[s]][XX[t]]
        assert A==Q
        checks[2]+=1;checks[3]+=bool(FR);checks[4]+=any(set(e)<=X for e in F)
        checks[5]+=any(s in e or t in e for e in F);checks[6]+=A is None
print("endpoint constraints / shared identity on both sides / failure queries / use head / internal fail / terminal fail / unreachable / tiled bank:",*checks)
