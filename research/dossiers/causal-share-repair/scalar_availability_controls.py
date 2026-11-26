"""Exhaustive public-algebra controls for availability, with no wire transport."""
from itertools import combinations, product
Q=11

def rank(A,n):
    A=[list(v) for v in A]
    r=0
    for j in range(n):
        piv=next((i for i in range(r,len(A)) if A[i][j]%Q),None)
        if piv is None: continue
        A[piv],A[r]=A[r],A[piv]
        u=pow(A[r][j],-1,Q)
        A[r]=[x*u%Q for x in A[r]]
        for i in range(r+1,len(A)):
            c=A[i][j]
            A[i]=[(x-c*y)%Q for x,y in zip(A[i],A[r])]
        r+=1
    return r

def ratio(H,a,b,i):
    u=H[i]
    c=1
    for h in H:
        if h!=u: c=c*(b-h)*pow((a-h)%Q,-1,Q)%Q
    return c

def exhaustive_rank():
    tests=0
    Hpool=list(range(3,9))
    for H in combinations(Hpool,4):
        edges=list(combinations(range(4),2))
        for mask in range(64):
            E=[e for i,e in enumerate(edges) if mask>>i&1]
            for c in range(3):
                for C in combinations(range(4),c):
                    live=[(u,v) for u,v in E if u not in C and v not in C]
                    # Orthogonal complement of visible equations is the
                    # hidden edge incidence space in weighted coordinates.
                    alpha=[ratio(H,1,0,u) for u in range(4)]
                    beta=[ratio(H,1,2,u) for u in range(4)]
                    A=[[alpha[u]-alpha[v] for u,v in live]]
                    B=[[beta[u]-beta[v] for u,v in live]]
                    assert (rank(A,len(live))==1)==bool(live)
                    products={(2-H[u])*(2-H[v])*pow((H[u]*H[v])%Q,-1,Q)%Q for u,v in live}
                    assert (rank(A+B,len(live))>rank(B,len(live)))==(len(products)>=2)
                    tests+=1
    return tests

def turan_controls():
    n=6
    Es=list(combinations(range(n),2))
    best=[99]*(n+1)
    masks_for_sizes=[set() for _ in range(n+1)]
    for h in range(2,n+1):
        for S in combinations(range(n),h):
            masks_for_sizes[h].add(sum(1<<i for i,(u,v) in enumerate(Es) if u in S and v in S))
    for graph in range(1<<len(Es)):
        k=graph.bit_count()
        for h in range(2,n+1):
            if k<best[h] and all(graph&x for x in masks_for_sizes[h]): best[h]=k
    for h in range(2,n+1):
        r,s=divmod(n,h-1)
        assert best[h]==s*(r+1)*r//2+(h-1-s)*r*(r-1)//2
    return best[2:]

if __name__=='__main__':
    print(exhaustive_rank(),'finite-field helper graph and exposure cases verified.')
    print('All 32768 six-vertex graphs: optimal scalar edge counts for honest sizes 2..6:',turan_controls())
