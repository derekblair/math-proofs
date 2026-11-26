"""Abstract synthetic checks of capsule counts, not KEM software."""
from itertools import product
from random import Random

def lmin(n,f,M):
    q,s=divmod(M,n)
    return f*q+min(f,s)

def scan(n,r,c,f):
    return next((m for m in range(1,n+1) if m>=c+1+lmin(n,f,r*m)),None)

def quotients(n,r,c,f):
    ceil=lambda x:(x+r-1)//r
    options=[]
    for l in range(r+1):
        low=max(1,ceil(n*l)); hi=min(n,ceil(n*(l+1))-1)
        if hi<low: continue
        if r*low-n*l<=f and low>=c+1+lmin(n,f,r*low):
            options.append(low)
        k=max(low,ceil(n*l+f),c+1+f*(l+1))
        if k<=hi:
            assert k>=c+1+lmin(n,f,r*k)
            options.append(k)
    return min(options,default=None)

def top(v,k):
    return sum(sorted(v,reverse=True)[:k])

def matrix_exhaustive():
    C=0
    for n,r in ((3,1),(4,2),(3,3),(2,4),(4,3)):
        # Full multiplicity 0,1,2 for smaller matrices, full binary at 4*3.
        maxw=3 if n*r<12 else 2
        opt={(c,f):None for c in range(n) for f in range(n)}
        for w in product(range(maxw),repeat=n*r):
            W=[w[i*n:(i+1)*n] for i in range(r)]
            E=[sum(row) for row in W]; M=sum(E)
            D=list(map(sum,zip(*W)))
            for f in range(n):
                L=top(D,f)
                assert L>=lmin(n,f,M)
                for c in range(n):
                    hide=max(M-x+top(row,c) for row,x in zip(W,E))
                    cut=all(x>=top(row,c)+L+1 for row,x in zip(W,E))
                    assert cut==(hide<M-L)
                    if cut:
                        m=scan(n,r,c,f)
                        assert m is not None and all(x>=m for x in E)
                        if opt[c,f] is None or M<opt[c,f]: opt[c,f]=M
                    C+=1
        for (c,f),k in opt.items():
            m=scan(n,r,c,f)
            assert (k is None and m is None) or k==r*m
    return C

def cyclic(n,r,m):
    rows=[{(i*m+j)%n for j in range(m)} for i in range(r)]
    assert all(len(row)==m for row in rows)
    d=[sum(x in row for row in rows) for x in range(n)]
    assert max(d)-min(d)<=1
    return d

def main():
    C=matrix_exhaustive()
    rr=Random(1942)
    for _ in range(22000):
        n=rr.randint(1,150); r=rr.randint(1,22)
        c=rr.randint(0,n); f=rr.randint(0,n)
        ans=scan(n,r,c,f)
        assert ans==quotients(n,r,c,f)
        assert (ans is not None)==(n>=c+r*f+1)
        if ans is not None:
            d=cyclic(n,r,ans)
            assert top(d,f)==lmin(n,f,r*ans)
            assert ans>=c+1+top(d,f)
            if n==c+r*f+1: assert ans==n
            if f: assert (ans==c+f+1)==(n>=r*(c+f+1))
    assert scan(9,3,2,2)==9
    assert scan(12,3,2,2)==7
    print(C,'exhaustive arithmetic layout/cut comparisons')
    print('22000 quotient-interval and cyclic-placement controls')
if __name__=='__main__': main()
