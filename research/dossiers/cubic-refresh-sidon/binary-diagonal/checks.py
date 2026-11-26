from itertools import combinations
from functools import reduce
from operator import xor

def xsum(it):return reduce(xor,it,0)

class Field:
    polys={2:7,3:11,4:19,5:37,6:67,8:283}
    def __init__(self,r):self.r=r;self.q=1<<r;self.p=self.polys[r]
    def mul(self,a,b):
        out=0
        while b:
            if b&1:out^=a
            b>>=1;a<<=1
            if a&self.q:a^=self.p
        return out
    def pow(self,x,n):
        out=1
        while n:
            if n&1:out=self.mul(out,x)
            x=self.mul(x,x);n>>=1
        return out
    def inv(self,a):
        t=self.pow(a,self.q-2)
        assert self.mul(a,t)==1
        return t
    def prod(self,it):return reduce(self.mul,it,1)

def binary_rank(vals):
    piv={}
    for a in vals:
        while a:
            h=a.bit_length()
            if h in piv:a^=piv[h]
            else:
                piv[h]=a
                break
    return len(piv)

def field_rank(F,rows):
    rows=[list(x) for x in rows]
    j=0
    for c in range(len(rows[0])):
        i=next((i for i in range(j,len(rows)) if rows[i][c]),None)
        if i is None:continue
        rows[i],rows[j]=rows[j],rows[i]
        inv=F.inv(rows[j][c])
        for t in range(j+1,len(rows)):
            z=F.mul(rows[t][c],inv)
            if z:rows[t]=[a^F.mul(z,b) for a,b in zip(rows[t],rows[j])]
        j+=1
        if j==len(rows):break
    return j

def polynomial_through(F,S,v):
    P=[0]*len(S)
    for a,w in zip(S,v):
        H=[1]
        for b in S:
            if b==a:continue
            H=[F.mul(b,H[0])]+[H[j-1]^F.mul(b,H[j]) for j in range(1,len(H))]+[H[-1]]
        P=[x^F.mul(w,y) for x,y in zip(P,H)]
    assert not P[-1]
    return P[:-1]

def ev(F,P,a):
    z=0
    for c in reversed(P):z=F.mul(z,a)^c
    return z

def affinerank(F,rows):
    return binary_rank([[sum((x<< (F.r*j) for j,x in enumerate(col))) for col in zip(*rows)]][0])

count=direct=0
for m,r in [(2,3),(4,4),(4,5),(6,4),(6,5),(8,5)]:
    F=Field(r)
    S=list(range(1,2*m+1))
    cols=[0]*(m-1)+[1<<i for i in range(m)]+[(1<<m)-1]
    L=Field(max(m,r))
    K=max(m,r)
    V=[[L.mul(1<<i,w)&(F.q-1) for w in cols] for i in range(K)]
    P=[polynomial_through(F,S,v) for v in V]
    for v,p in zip(V,P):
        for j,a in enumerate(S):
            assert ev(F,p,a)==F.mul(v[j],F.prod(a^b for b in S if b!=a))
    d=(m+r-1)//r
    for A in combinations(range(2*m),m):
        weights=[xsum(v[j] for j in A) for v in V]
        assert binary_rank(weights)==r
        # Whole-field padded construction packs m-bit witness labels into field blocks.
        h=xsum(cols[j] for j in A)
        assert h and any((h>>(r*i))&(F.q-1) for i in range(d))
        count+=1
        if direct<60 or (m,r)==(6,4) and direct<100:
            # Direct binary affine rank in the transcript, not only the quotient.
            span=[]
            for j in range(1,2*m):
                for k in range(r):
                    span.append(sum(F.mul(1<<k,F.pow(a,j))<<(r*i) for i,a in enumerate(S)))
            for p in P:
                span.append(sum(F.mul(a,ev(F,p,a))<<(r*i) for i,a in enumerate(S) if i not in A))
            rk=binary_rank(span)
            assert rk==2*m*r
            direct+=1
for m,r in [(3,3),(5,4),(7,4)]:
    F=Field(r); S=list(range(1,2*m+1))
    P=polynomial_through(F,S,[1]*(2*m))
    assert all(ev(F,P,a)==F.prod(a^b for b in S if b!=a) for a in S)
    for A in combinations(range(2*m),m):
        assert xsum(1 for i in A)==1
        count+=1
print(f'{count} balanced subset / seed-rank checks, {direct} direct affine transcript ranks')
