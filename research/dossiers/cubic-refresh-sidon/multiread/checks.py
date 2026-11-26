from itertools import combinations,product

class Field:
    def __init__(self,p,quad=False):
        self.p=p; self.q=p*p if quad else p
        self.d=next((x for x in range(1,p) if x not in {a*a%p for a in range(p)}),1)
    def add(self,x,y):
        p=self.p
        return (x+y)%p+p*((x//p+y//p)%p)
    def neg(self,x):
        p=self.p
        return (-x%p)+p*((-(x//p))%p)
    def sub(self,x,y):return self.add(x,self.neg(y))
    def mul(self,x,y):
        p=self.p
        a,b=x%p,x//p; c,d=y%p,y//p
        if self.q==p:return a*c%p
        return ((a*c+self.d*b*d)%p)+p*((a*d+b*c)%p)
    def pow(self,x,n):
        a=1
        for i in range(n):a=self.mul(a,x)
        return a
    def prod(self,V):
        a=1
        for v in V:a=self.mul(a,v)
        return a
    def sum(self,V):
        a=0
        for v in V:a=self.add(a,v)
        return a
    def div(self,a,b):
        assert b
        return self.mul(a,self.pow(b,self.q-2))
    def scalar(self,n):return n%self.p

def rank(A,F):
    A=[list(a) for a in A]
    r=0
    for j in range(len(A[0])):
        pivot=next((i for i in range(r,len(A)) if A[i][j]),None)
        if pivot is None:continue
        A[r],A[pivot]=A[pivot],A[r]
        for i in range(r+1,len(A)):
            if not A[i][j]:continue
            c=F.div(A[i][j],A[r][j])
            A[i]=[F.sub(x,F.mul(c,y)) for x,y in zip(A[i],A[r])]
        r+=1
        if r==len(A):break
    return r

def evalp(F,P,a):
    u=0
    for c in reversed(P):u=F.add(F.mul(u,a),c)
    return u

def poly_no(F,S):
    # Monic product over roots
    P=[1]
    for a in S:
        R=[F.neg(F.mul(a,P[0]))]
        R += [F.sub(P[i-1],F.mul(a,P[i])) for i in range(1,len(P))]
        R.append(P[-1])
        P=R
    return P

def dense_view_rank(F,A,B,W):
    m=len(A)
    M=[]
    for j,V in enumerate((A,B)):
        for x in V:
            M.append([F.pow(x,k) for k in range(1,2*m)]+
                     [F.mul(x,evalp(F,W,x)) if j else 0])
    return rank(M,F)==rank([row+[1] for row in M],F)

def phi(F,A,B,W):
    C=A+B
    return F.sum(F.div(evalp(F,W,a),F.prod(F.sub(a,b) for b in C if b!=a))
                 for a in A)

def diag(F,S):
    n=len(S); m=n//2
    v={a:1 if i else F.scalar(1-n) for i,a in enumerate(S)}
    W=[0]*n
    for a in S:
        Ra=poly_no(F,[b for b in S if a!=b])
        W=[F.add(x,F.mul(v[a],y)) for x,y in zip(W,Ra)]
    assert W[-1]==0 and any(W)
    W.pop()
    return W,v

count=0
for F in [Field(p) for p in (5,7,11,13,17,19,23,29)]+[Field(3,True)]:
    for m in range(2,min(7,(F.q-1)//2)+1):
        if not (m%F.p):continue
        for S in {tuple(range(1,2*m+1)),tuple(range(F.q-2*m,F.q))}:
            W,v=diag(F,S)
            for A in combinations(S,m):
                B=tuple(b for b in S if b not in A)
                value=F.sum(v[a] for a in A)
                assert value and phi(F,A,B,W)==value
                if m<=4:assert dense_view_rank(F,A,B,W)
                count+=1

views=0
for p,n,m in [(7,6,3),(11,8,3),(11,8,4),(13,9,3)]:
    F=Field(p)
    S=tuple(range(1,n+1))
    Rprime={a:F.prod(F.sub(a,b) for b in S if a!=b) for a in S}
    for j in range(9):
        W=[(u*u*(j+1)+u*j+1)%p for u in range(2*m-1)]
        v={a:F.div(evalp(F,W,a),Rprime[a]) for a in S}
        for k in range(n-2*m+1):
            assert F.sum(F.mul(F.pow(a,k),v[a]) for a in S)==0
        for C in combinations(S,2*m):
            D=tuple(d for d in S if d not in C)
            for A in combinations(C,m):
                B=tuple(b for b in C if b not in A)
                g=F.sum(F.mul(v[a],F.prod(F.sub(a,d) for d in D)) for a in A)
                assert phi(F,A,B,W)==g and (g!=0)==dense_view_rank(F,A,B,W)
                views+=1
print(count,'diagonal field/view checks;',views,'general moment/actual affine-rank checks')
