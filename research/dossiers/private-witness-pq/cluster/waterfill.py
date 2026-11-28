"""Exact private-support minimax and layout optimization for synthetic counts."""
from bisect import bisect_left
from fractions import Fraction as Fq
from functools import cache,reduce
from math import comb,lcm

C,F,N=63,6,130
R=F+1

@cache
def probs(n,r):
    # increasing probability order; at index i, exposures k-i
    k=n-r+1
    den=comb(n,r)
    return tuple(Fq(comb(r-1+i,r),den) for i in range(k+1))

def demand(n,r,L):
    p=probs(n,r); k=len(p)-1
    at=bisect_left(p,L)
    if p[at]==L:return Fq(k-at)
    assert 0<at<=k
    return k-at + (p[at]-L)/(p[at]-p[at-1])

def level(layout,c,r):
    if c==0:return Fq(1)
    if c>=sum(n-r+1 for n in layout):return Fq(0)
    events=sorted(set().union(*(probs(n,r) for n in layout)))
    lo=0; hi=len(events)-1
    while hi-lo>1:
        j=(lo+hi)//2; L=events[j]
        total=sum(demand(n,r,L) for n in layout)
        if total==c:return L
        if total>c:lo=j
        else:hi=j
    L,U=events[lo],events[hi]
    dl,du=[sum(demand(n,r,V) for n in layout) for V in (L,U)]
    assert dl>=c>=du and dl>du
    lam=L+(U-L)*(dl-c)/(dl-du)
    assert sum(demand(n,r,lam) for n in layout)==c
    return lam

def best_at(lam,c,f,nmax,dcap):
    r=f+1
    a=[Fq(0)]*r+[demand(n,r,lam) for n in range(r,nmax+1)]
    L=reduce(lcm,(x.denominator for x in a),1)
    a=[int(x*L) for x in a]
    layers=[{0:(0,0)}]
    best=None
    for g in range(1,nmax//r+1):
        row={}
        # Keep only states that could still reach the recovery cap.
        for spent,(prev,_) in layers[-1].items():
            for x in range(r,min(nmax-spent,dcap-(spent-(g-1)*f)+f)+1):
                score=prev+a[x]; n=spent+x
                if n not in row or score>row[n][0]:
                    row[n]=(score,x)
        layers.append(row)
        for n,(v,_) in row.items():
            if c<n-g*f<=dcap and (best is None or v>best[0]):
                best=(v,g,n)
    assert best is not None
    score,g,n=best
    out=[]
    for i in range(g,0,-1):
        x=layers[i][n][1]; n-=x; out.append(x)
    assert n==0
    return Fq(score,L),tuple(sorted(out))

def solve(c,f,n,dcap,start=None):
    if start is None:
        _,start=best_at(Fq(1,2),c,f,n,dcap)
    L=level(start,c,f+1)
    path=[]
    while True:
        score,other=best_at(L,c,f,n,dcap)
        assert score>=c
        path.append((L,start))
        if score==c:return L,start,len(path)
        start=other
        z=level(start,c,f+1)
        assert z>L
        L=z

if __name__=='__main__':
    for D in (64,70,76,80,82,84,88,92,100,112,124):
        L,A,steps=solve(C,F,N,D)
        print(D,'=>',sum(A),sum(A)-F*len(A),1/L,float(1/L),A,'iterations',steps)
    for A in ((20,19,19,18,18,18,18),(130,), (9,)*6+(76,), (15,15)+(20,)*5):
        L=level(A,C,R)
        print('fixed',A,'loss',1/L,float(1/L))
