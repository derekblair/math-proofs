"""Fixed synthetic finite-field rank controls; no KEM or transport."""
from itertools import combinations, product

def rank(A,p):
    if not A: return 0
    A=[list(r) for r in A]; d=0
    for j in range(len(A[0])):
        k=next((i for i in range(d,len(A)) if A[i][j]%p),None)
        if k is None: continue
        A[d],A[k]=A[k],A[d]
        u=pow(A[d][j]%p,-1,p)
        A[d]=[u*x%p for x in A[d]]
        for i in range(d+1,len(A)):
            c=A[i][j]%p
            A[i]=[(x-c*y)%p for x,y in zip(A[i],A[d])]
        d+=1
    return d

def row(p,t,x,j,U):
    X=[pow(x,k,p) for k in range(1,t+1)]
    return [1]+X+[sum(a*a1 for a,a1 in zip(X,v))%p if e<j else 0
                 for e,Ue in enumerate(U) for v in Ue]

def old(p,t,S,U):
    a,b,c=S
    return ([row(p,t,x,0,U) for x in a]
            +[row(p,t,x,j,U) for x in b for j in (0,1)]
            +[row(p,t,x,j,U) for x in c for j in (1,2)])

def clean(p,t,S,U):
    return [row(p,t,x,j,U) for j,T in enumerate(S) for x in T]

def safe(A,p):
    return rank(A,p)==rank([a[1:] for a in A],p)

def allviews(n,bs):
    return list(product(*(combinations(range(1,n+1),b) for b in bs)))

def main():
    p=5;t=2
    V=allviews(4,[1,1,1])
    cols=list(product(range(p),repeat=t))
    n=0
    for u,v in product(cols,repeat=2):
        raw=[safe(old(p,t,S,((u,),(v,))),p) for S in V]
        no_last=[safe(old(p,t,S,((u,),())),p) for S in V]
        assert raw==no_last
        assert not all(raw)
        n+=len(V)
    assert all(safe(old(p,t,S,(((1,0),(0,1)),())),p) for S in V)
    assert any(all(safe(clean(p,t,S,((u,),())),p) for S in V) for u in cols)
    assert not all(safe(clean(p,t,S,((),())),p) for S in V)

    p=7;t=3
    V2=allviews(5,[1,1,2])
    cols=list(product(range(p),repeat=t))
    for u in cols:
        assert not all(safe(old(p,t,S,((u,),())),p) for S in V2)
    witnesses=[
        ((1,0,0),(0,1,0)),
        ((1,0,0),(0,0,1)),
        ((0,1,0),(0,0,1)),
    ]
    best=next((U for U in witnesses if all(safe(old(p,t,S,(U,())),p) for S in V2)),None)
    if best is None:
        best=next(U for U in combinations(cols[1:],2) if all(safe(old(p,t,S,(U,())),p) for S in V2))
    print(n,'GF5 comparisons; final-seam irrelevance and one-coin lower bound.')
    print('Exact GF5 high-level example: one clean vs two stale coins.')
    print('GF7 degree-three b=(1,1,2): all 343 one-column choices fail; two columns work:',best)

if __name__=='__main__': main()
