from fractions import Fraction as F
from random import Random
from itertools import permutations

def initial(P):
    return tuple((F(min(p[j] for p in P)-1),F(max(p[j] for p in P)+1)) for j in range(len(P[0])))

def clip(p,q,B):
    a,b=F(0),F(1)
    for x,y,(l,h) in zip(p,q,B):
        if x==y:
            if not l<=x<=h:return None
        else:
            u,v=sorted(((l-x)/(y-x),(h-x)/(y-x)))
            a,b=max(a,u),min(b,v)
            if a>b:return None
    return a,b

def within(p,B):
    return all(a<=x<=b for x,(a,b) in zip(p,B))

def choose(P,E,B):
    d=len(B);j=max(range(d),key=lambda j:B[j][1]-B[j][0])
    L,H=B[j]; W=H-L; a,b=L+W/3,H-W/3
    ev={a,b}; spans={};by_chain={}
    def zz(i,z):return z[i] if i<d else F(0)
    integral=F(0)
    for t,(i,u,v) in enumerate(E):
        p,q=P[u],P[v]
        Q=clip(p,q,B)
        if Q is None:continue
        l,h=Q
        pos=lambda s:tuple(x+s*(y-x) for x,y in zip(p,q))
        z,zp=pos(l),pos(h)
        lo,hi=sorted([z[j],zp[j]])
        if a<lo<b:ev.add(lo)
        if a<hi<b:ev.add(hi)
        if lo<hi:
            spans[t]=(lo,hi)
            integral+=max(F(0),min(hi,b)-max(lo,a))
        du=zz(i,zp)-zz(i,z);dv=du-(zp[j]-z[j])
        assert du>=0 and dv>=0 and hi-lo<=du+dv
        u0,v0=by_chain.get(i,(F(0),F(0)))
        by_chain[i]=u0+du,v0+dv
    assert all(A<=W and V<=2*W for A,V in by_chain.values())
    assert integral<=3*(d+1)*W
    ev.update(x[j] for x in P if a<x[j]<b)
    A=sorted(ev)
    best=None
    for l,h in zip(A,A[1:]):
        c=(l+h)/2
        touched={t for t,(lo,hi) in spans.items() if lo<c<hi}
        if best is None or len(touched)<len(best[1]):best=c,touched
    c,S=best
    assert a<c<b and all(p[j]!=c for p in P) and len(S)<=9*(d+1)
    return j,c,S

def verify(P,paths):
    P=[tuple(map(F,p)) for p in P]; k=len(paths)
    E=[(i,a,b) for i,L in enumerate(paths) for a,b in zip(L,L[1:])]
    B0=initial(P); counts=dict(boxes=0,nonlocal_crosses=0,empty=0,polyties=0,nonroot_faces_used=0,maxboundary=0)
    stack=[(B0,{})]
    while stack:
        B,H=stack.pop();counts['boxes']+=1
        X={v for v,p in enumerate(P) if within(p,B)}
        if not X:continue
        C={t for t,(i,u,v) in enumerate(E) if (u in X)!=(v in X)}
        counts["maxboundary"]=max(counts["maxboundary"],len(C))
        assert len(C)<=18*k*(k-1)
        for t in C:
            i,u,v=E[t];p,q=P[u],P[v]; yes=False
            for (j,s),touched in H.items():
                if q[j]==p[j]:continue
                c=B[j][s];h=(c-p[j])/(q[j]-p[j])
                if 0<h<1 and within(tuple(x+h*(y-x) for x,y in zip(p,q)),B):
                    assert t in touched
                    yes=True
            assert yes
            counts['nonroot_faces_used']+=1
        if len({P[v] for v in X})<=1:
            counts['polyties']+=len(X)>1;continue
        j,c,touch=choose(P,E,B)
        counts['nonlocal_crosses']+=sum(not(within(P[u],B) and within(P[v],B)) for t in touch for _,u,v in [E[t]])
        for side in (0,1):
            H1=H|{(j,1-side):touch}
            D=list(B);D[j]=(B[j][0],c) if side==0 else (c,B[j][1])
            C=tuple(D)
            if not any(within(p,C) for p in P):
                counts['empty']+=1
            else:stack.append((C,H1))
    return counts

def generate(K,rng):
    P=[];paths=[]
    for i in range(K):
        pv=[rng.randint(-20,20) for j in range(K)]
        L=[]
        for t in range(rng.randrange(3,13)):
            L.append(len(P));P.append([x-pv[-1] for x in pv[:-1]])
            own=rng.randint(1,10)
            pv=[x+own-(0 if h==i or rng.randrange(7)==0 else rng.randint(0,15)) for h,x in enumerate(pv)]
        paths.append(L)
    # Decoys including exact tied positions at internal nodes.
    for _ in range(9):
        P.append(list(rng.choice(P)) if rng.randrange(2) else [rng.randint(-90,90) for i in range(K-1)])
    return P,paths

if __name__=='__main__':
    from collections import Counter
    R=Random(9642);n=0;stats=Counter()
    for k in range(2,8):
        for case in range(18):
            P,W=generate(k,R)
            z=verify(P,W);n+=1
            m=max(stats['maxboundary'],z['maxboundary'])
            stats.update(z);stats['maxboundary']=m
    print(n,dict(stats))
