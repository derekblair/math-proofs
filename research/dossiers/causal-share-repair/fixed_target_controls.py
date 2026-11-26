"""Synthetic tests for the prescribed visible-repair schedule theorem."""
from itertools import product

Q=7

def greedy(xs,t):
    seen=set()
    ends=[0]
    for i,x in enumerate(xs):
        if x not in seen and len(seen)==t:
            ends.append(i)
            seen.clear()
        seen.add(x)
    return ends+[len(xs)]

def valid_cuts(xs,t,cuts):
    return all(len(set(xs[a:b]))<=t for a,b in zip(cuts,cuts[1:]))

def root_product(xs,t):
    p=[1]
    for a in sorted(set(xs)):
        b=-pow(a,-1,Q)
        v=p+[0]
        for i,x in enumerate(p):
            v[i+1]=(v[i+1]+b*x)%Q
        p=v
    return p+[0]*(t+1-len(p))

def evaluate(p,x):
    return sum(a*x**i for i,a in enumerate(p))%Q

def rank(A):
    A=[list(a) for a in A]; r=0
    for j in range(len(A[0])):
        p=next((i for i in range(r,len(A)) if A[i][j]%Q),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        u=pow(A[r][j],-1,Q)
        A[r]=[u*a%Q for a in A[r]]
        for i in range(r+1,len(A)):
            c=A[i][j]
            A[i]=[(a-c*b)%Q for a,b in zip(A[i],A[r])]
        r+=1
    return r

def check(xs,t):
    G=greedy(xs,t)
    assert valid_cuts(xs,t,G)
    best=len(xs)-1
    for mask in range(1<<(len(xs)-1)):
        k=mask.bit_count()
        if k>=best: continue
        if valid_cuts(xs,t,[0]+[i+1 for i in range(len(xs)-1) if mask>>i&1]+[len(xs)]):
            best=k
    assert len(G)-2==best
    polys=[root_product(xs[a:b],t) for a,b in zip(G,G[1:])]
    for p,a,b in zip(polys,G,G[1:]):
        assert p[0]==1 and {x for x in range(Q) if evaluate(p,x)==0}==set(xs[a:b])
    diffs=[[ (b-a)%Q for a,b in zip(v,w)] for v,w in zip(polys,polys[1:])]
    for g,j in zip(diffs,G[1:-1]):
        assert not g[0] and evaluate(g,xs[j])!=0
    obs=[[pow(x,j,Q) for j in range(1,t+1)]+
         [evaluate(g,x) if i>=j else 0 for g,j in zip(diffs,G[1:-1])] for i,x in enumerate(xs)]
    assert rank(obs)==rank([a+[1] for a in obs])

if __name__=='__main__':
    tests=0
    for L in range(1,7):
        for xs in product(range(1,5),repeat=L):
            for t in (1,2,3):
                check(xs,t)
                tests+=1
    print(tests,'target/degree combinations: partition optimum, exact roots, rank privacy, seam rank all checked.')
