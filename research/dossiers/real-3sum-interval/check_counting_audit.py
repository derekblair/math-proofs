"""Independent exact cut, staircase, and distinct-index controls."""
from itertools import product
from random import Random
from collections import Counter

def scan(A,B,c,d,high):
    a=sorted((x,i+1) for i,x in enumerate(A))
    b=sorted((x,(j+1)*(len(a)+1)) for j,x in enumerate(B))
    tag=(len(a)+1)*(len(b)+1)
    q=(c,tag if high else 0)
    X=[a[i:i+d] for i in range(0,len(a),d)]
    Y=[b[j:j+d] for j in range(0,len(b),d)]
    def add(u,v): return (u[0]+v[0],u[1]+v[1])
    pref=[0]
    for Z in Y: pref.append(pref[-1]+len(Z))
    jlo=jhi=len(Y)
    total=0; slices=[]
    for i,Z in enumerate(X):
        while jlo and add(Z[-1],Y[jlo-1][-1])>=q: jlo-=1
        while jhi and add(Z[0],Y[jhi-1][0])>=q: jhi-=1
        assert 0<=jlo<=jhi<=len(Y)
        total+=len(Z)*pref[jlo]
        for j in range(jlo,jhi):
            sums=sorted(add(u,v) for u,v in product(Z,Y[j]))
            assert sums[0]<q<=sums[-1]
            pred=max(u for u in sums if u<q)
            rank=1+sums.index(pred)
            total+=rank
            slices.append(i-j)
    assert len(slices)==len(set(slices))
    return total

def run():
    rng=Random(1532)
    for _ in range(1200):
        A=[rng.randrange(-3,4) for __ in range(rng.randrange(0,17))]
        B=[rng.randrange(-3,4) for __ in range(rng.randrange(0,17))]
        d=rng.randrange(1,8)
        c=rng.randrange(-7,8)
        assert scan(A,B,c,d,True)-scan(A,B,c,d,False)==sum(a+b==c for a,b in product(A,B))
        f=Counter(A)
        for k,x in enumerate(A):
            raw=sum(a+b==x for a,b in product(A,A))
            correction=sum(freq for y,freq in f.items() if y+y==x)+2*f[0]-2*(x==0)
            assert raw-correction==sum(A[i]+A[j]==x for i,j in product(range(len(A)),repeat=2) if len({i,j,k})==3)
    print('1200 arbitrary-height cut controls plus every single-list target correction')
if __name__=='__main__': run()
