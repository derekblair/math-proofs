from itertools import combinations, product

def rank(rows, F):
    A=[list(r) for r in rows]
    j=0
    for c in range(len(A[0])):
        pivot=next((i for i in range(j,len(A)) if A[i][c]),None)
        if pivot is None: continue
        A[j],A[pivot]=A[pivot],A[j]
        inv=F.pow(A[j][c],F.q-2)
        for i in range(j+1,len(A)):
            if A[i][c]:
                u=F.mul(A[i][c],inv)
                A[i]=[F.sub(x,F.mul(u,y)) for x,y in zip(A[i],A[j])]
        j+=1
        if j==len(A): break
    return j

class Field:
    def __init__(self,p,quad=False):
        self.p=p
        self.q=p*p if quad else p
        self.d=next((x for x in range(1,p) if x not in {a*a%p for a in range(p)}),1)
    def add(self,x,y):
        p=self.p
        return ((x%p+y%p)%p) + p*((x//p+y//p)%p)
    def neg(self,x):
        p=self.p
        return (-x%p)+p*((-(x//p))%p)
    def sub(self,x,y): return self.add(x,self.neg(y))
    def mul(self,x,y):
        p=self.p
        a,b=x%p,x//p
        c,d=y%p,y//p
        if self.q==p: return a*c%p
        if p==2: return ((a*c+b*d)%2)+2*((a*d+b*c+b*d)%2)
        return ((a*c+self.d*b*d)%p)+p*((a*d+b*c)%p)
    def pow(self,x,j):
        y=1
        while j:
            if j&1: y=self.mul(x,y)
            j//=2
            x=self.mul(x,x)
        return y

def privacy(F,A,B,Q):
    M=[]
    for e,E in enumerate((A,B)):
        for x in E:
            v=[x,F.pow(x,2),F.pow(x,3)]
            refresh=F.add(F.add(F.mul(v[0],Q[0]),F.mul(v[1],Q[1])),F.mul(v[2],Q[2])) if e else 0
            M.append(v+[refresh])
    return rank(M,F)==rank([v+[1] for v in M],F)

def poly(F,a,b):
    return [F.mul(a,b),F.neg(F.add(a,b)),1]

def partitions(S):
    a,b,c,d=S
    yield (a,b),(c,d)
    yield (a,c),(b,d)
    yield (a,d),(b,c)

N=0
for p in (5,7,11):
    F=Field(p)
    Ws=[(1,b,c) for b,c in product(range(p),repeat=2)]+[(0,1,c) for c in range(p)]+[(0,0,1)]
    for W in Ws:
        for T in combinations(range(1,p),4):
            for A,B in partitions(T):
                actual=privacy(F,A,B,W)
                pred=rank([poly(F,*A),poly(F,*B),list(W)],F)==3
                assert actual==pred,(p,A,B,W,actual,pred)
                N+=1
    if p==7:
        assert all(any(not privacy(F,A,B,W) for T in combinations(range(1,p),4)
                       for A,B in partitions(T)) for W in Ws)

M=0
for p in (5,7,11,13):
    F=Field(p,True)
    W=(1,p,0)
    for T in combinations(range(1,p),4):
        for A,B in partitions(T):
            assert privacy(F,A,B,W)
            M+=1
print(N,'projective/linear-view cross-checks;',M,'explicit quadratic-field controls')
