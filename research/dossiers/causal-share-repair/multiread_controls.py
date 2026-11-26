"""Synthetic finite graph/rank controls for multiread repair."""
from itertools import combinations
from collections import defaultdict

def rank(rows,p,n):
    A=[list(row) for row in rows]; k=0
    for j in range(n):
        w=next((w for w in range(k,len(A)) if A[w][j]%p),None)
        if w is None: continue
        A[w],A[k]=A[k],A[w]
        c=pow(A[k][j]%p,-1,p)
        A[k]=[v*c%p for v in A[k]]
        for i in range(k+1,len(A)):
            v=A[i][j]
            A[i]=[(x-v*y)%p for x,y in zip(A[i],A[k])]
        k+=1
    return k

def components(n,E):
    adj=[[] for i in range(n)]
    for i,j in E: adj[i].append(j);adj[j].append(i)
    C=[]; left=set(range(n))
    while left:
        S={left.pop()}; stack=list(S)
        while stack:
            for j in adj[stack.pop()]:
                if j in left:
                    left.remove(j);S.add(j);stack.append(j)
        C.append(sorted(S))
    return C

def safe(E,L,reads,p):
    row=lambda b:[pow(((b-L[u])*(b-L[v]))%p,-1,p) for u,v in E]
    A=[row(b) for b in reads]
    return rank(A+[row(0)],p,len(E))>rank(A,p,len(E))

def fibers(p,d):
    A=defaultdict(list)
    for x in range(1,p-1): A[(pow(x+1,d,p)-1)%p].append(x)
    B=A.pop(0)
    fs=[sites for value,sites in A.items() if len(sites)==d]
    assert len(B)==d-1 and len(fs)>=5
    return B, fs

def main():
    tests=0
    n=5
    edges=list(combinations(range(n),2))
    for p,d in ((13,2),(31,3),(41,4)):
        reads,fs=fibers(p,d)
        for mask in range(1<<len(edges)):
            E=[e for i,e in enumerate(edges) if mask>>i&1]
            C=components(n,E)
            good=max(map(len,C))>d
            if good:
                L=[x for x in range(1,p-1) if x not in reads][:n]
            else:
                L=[None]*n
                for S,T in zip(C,fs):
                    for i,x in zip(S,T): L[i]=x
            assert len(set(L))==n and set(L).isdisjoint({0,p-1,*reads})
            assert safe(E,L,reads,p)==good
            tests+=1
    limits={}
    n=6
    edges=list(combinations(range(n),2))
    subsets=[]
    for u in range(n):
        Z=[(i-(i>u),j-(j>u),l) for l,(i,j) in enumerate(edges) if i!=u and j!=u]
        subsets.append(Z)
    for d in (2,3,4):
        for cap in range(1,d+3):
            any_pass=False
            for links in combinations(range(len(edges)),cap):
                linkset=set(links)
                if all(max(map(len,components(n-1,[(i,j) for i,j,l in Z if l in linkset])))>d for Z in subsets):
                    any_pass=True;break
            if any_pass:
                assert cap==d+2
                limits[d]=cap
                break
    print(tests,'five-vertex graph/field cases: constructed failures and guaranteed-safe ranks checked.')
    print('Six-vertex exact single-deletion relation optima (d=2,3,4):',limits)
if __name__=='__main__': main()
