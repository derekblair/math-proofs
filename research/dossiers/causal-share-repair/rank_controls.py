"""Local synthetic finite-field verification of causal prefix ranks."""
from random import Random
p=11

def rref(A,n):
    A=[list(row) for row in A]
    piv=[]
    for j in range(n):
        i=len(piv)
        k=next((k for k in range(i,len(A)) if A[k][j]%p),None)
        if k is None: continue
        A[k],A[i]=A[i],A[k]
        u=pow(A[i][j],-1,p)
        A[i]=[x*u%p for x in A[i]]
        for k in range(len(A)):
            if k==i: continue
            c=A[k][j]
            A[k]=[(a-c*b)%p for a,b in zip(A[k],A[i])]
        piv.append(j)
    return A[:len(piv)],piv

def ker(A,n):
    R,P=rref(A,n)
    B=[]
    for j in range(n):
        if j in P: continue
        x=[0]*n
        x[j]=1
        for i,k in enumerate(P):
            x[k]=-R[i][j]%p
        B.append(x)
    return B

def dot(x,y):
    return sum(a*b for a,b in zip(x,y))%p

def controls(t, targets, U):
    E=len(targets)
    # Use evaluation of each polynomial at t+1 live sites as transcript
    # coordinates, scaling each by exact Lagrange weights.
    histories=[]
    kernels=[]
    for e in range(1,E+1):
        cols=[(0,[int(i==j) for i in range(t+1)]) for j in range(t+1)]
        for j in range(e-1):
            cols += [(j+1,[0]+u) for u in U[j]]
        row_a=[]
        samples=[]
        for i,a in enumerate(targets[:e]):
            row_a.append([dot([pow(a,j,p) for j in range(t+1)],v) if start<=i else 0 for start,v in cols])
            hs=[x for x in range(1,p) if x!=a][:t+1]
            for h in hs:
                L=1
                for x in hs:
                    if x!=h: L*= (a-x)*pow((h-x)%p,-1,p)
                samples.append([(L*dot([pow(h,j,p) for j in range(t+1)],v))%p if start<=i else 0 for start,v in cols])
        k=[[dot(row,v) for row in samples] for v in ker(row_a,len(cols))]
        assert all(sum(kv[i:i+t+1])%p==0 for kv in k for i in range(0,len(kv),t+1))
        assert len(rref(k,e*(t+1))[1])==len(k)
        kernels.append(k)
        histories.append(row_a)
    W=list(kernels[-1])
    for e in range(E-1,0,-1):
        sz=e*(t+1)
        S=rref([w[:sz] for w in W],sz)[0]
        for x in kernels[e-1]:
            Splus=rref(S+[x],sz)[0]
            if len(Splus)>len(S):
                W.append(x+[0]*((E-e)*(t+1)))
                S=Splus
    for e in range(1,E+1):
        sz=e*(t+1)
        V=[w[:sz] for w in W]
        r=len(rref(V,sz)[0])
        assert r==len(rref(V+kernels[e-1],sz)[0])
    expected=t+sum(len(u)-int(any(row) ) for u,a in zip(U,targets[1:])
                   for row in [[dot(v,[pow(a,j,p) for j in range(1,t+1)]) for v in u]])
    assert len(W)==expected
    assert len(rref(W,E*(t+1))[0])==expected
    return len(kernels[-1]),expected

def main():
    assert controls(3,[1,2],[[]])==(2,3)
    assert controls(3,[1,1],[[]])==(3,3)
    assert controls(3,[1,2],[[[1,0,0]]])==(3,3)
    rng=Random(1709)
    for _ in range(1000):
        t=rng.randrange(1,6)
        E=rng.randrange(1,7)
        targets=[rng.randrange(1,p) for _ in range(E)]
        U=[rref([[rng.randrange(p) for _ in range(t)] for _ in range(rng.randrange(t+1))],t)[0] for i in range(E-1)]
        controls(t,targets,U)
    print('1000 random synthetic fixed schedules plus 3 exact controls passed.')
    print('No-refresh distinct-target t=3: offline 2, causal 3 field elements.')
if __name__=='__main__': main()
