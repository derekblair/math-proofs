from itertools import combinations, product
# Reuse the arithmetic and rank helpers without running the independent sweep.
from pathlib import Path
exec(Path(__file__).with_name('checks.py').read_text().split('\nN=0\n')[0])

def div(F,a,b):
    assert b
    return F.mul(a,F.pow(b,F.q-2))

def ev(F,W,r):
    return F.add(F.add(W[0],F.mul(W[1],r)),F.mul(W[2],F.mul(r,r)))

def get(F,W):
    if not W[2]:
        if not W[1]:return F, set(), lambda a:a, F.add, 'infdouble'
        r=div(F,F.neg(W[0]),W[1])
        return F,{r},lambda a:F.sub(r,a),F.mul,'splitinf'
    roots=[r for r in range(F.q) if ev(F,W,r)==0]
    if len(roots)==1:
        r=roots[0]
        return F,{r},lambda a:div(F,1,F.sub(r,a)),F.add,'double'
    if len(roots)==2:
        r,s=roots
        return F,{r,s},lambda a:div(F,F.sub(r,a),F.sub(s,a)),F.mul,'split'
    G=Field(F.p,True)
    r=next(r for r in range(G.q) if ev(G,W,r)==0)
    s=G.pow(r,F.q)
    return G,set(),lambda a:div(G,G.sub(r,a),G.sub(s,a)),G.mul,'conjugate'

checks=0
types=set()
for p in (5,7,11):
    F=Field(p)
    Ws=[(1,b,c) for b,c in product(range(p),repeat=2)]+[(0,1,c) for c in range(p)]+[(0,0,1)]
    examples={}
    for W in Ws:
        G,roots,lab,op,name=get(F,W)
        types.add(name)
        for n in range(4,min(6,p-1)+1):
            for S in combinations(range(1,p),n):
                good1=all(rank([poly(F,*A),poly(F,*B),list(W)],F)==3 
                          for T in combinations(S,4) for A,B in partitions(T))
                reg=tuple(a for a in S if a not in roots)
                vals=[op(lab(a),lab(b)) for a,b in combinations(reg,2)]
                good2=len(S)-len(reg)<=1 and len(vals)==len(set(vals))
                assert good1==good2,(p,S,W,name)
                if good2: examples[(name,n)]=(S,W)
                checks+=1
    print(p,examples)
assert len(types)==5

class GF8:
    q=8
    add=sub=staticmethod(lambda a,b:a^b)
    @staticmethod
    def mul(a,b):
        out=0
        while b:
            if b&1:out^=a
            a<<=1
            if a&8:a^=11
            b>>=1
        return out
    def pow(self,x,j): return Field.pow(self,x,j)
F=GF8()
r=1
S=[r]+[F.sub(r,div(F,1,z)) for z in (2,3,4,6)]
assert len(S)==len(set(S))==5 and all(S)
W=(1,0,1)
assert all(privacy(F,A,B,W) for T in combinations(S,4) for A,B in partitions(T))
print('GF8 example',S,'W:',W)
print(checks,'exact classifications, all five root types')
from collections import Counter
cases=0
for q in range(3,15):
    inv=(q%2==0)
    for m in range(2,q+1):
        for S in combinations(range(q),m):
            sums={(x+y)%q for x,y in combinations(S,2)}
            if len(sums)!=m*(m-1)//2: continue
            diffs=Counter((x-y)%q for x in S for y in S if x!=y)
            collision=sum(u*(u-1)//2 for u in diffs.values())
            assert collision<=2*m+inv
            assert q>=m*(m-1)-2*m+1-inv
            cases+=1
print(cases,'weak Sidon cyclic difference collision controls')
class GF16(GF8):
    q=16
    @staticmethod
    def mul(a,b):
        out=0
        while b:
            if b&1:out^=a
            a<<=1
            if a&16:a^=19
            b>>=1
        return out
F=GF16()
r=div(F,1,4)
S=[r]+[F.sub(r,div(F,1,z)) for z in (3,2,1,7,11,12)]
assert len(S)==len(set(S))==7 and all(S)
W=(F.mul(r,r),0,1)
assert all(privacy(F,A,B,W) for T in combinations(S,4) for A,B in partitions(T))
print('GF16 exact n=7 example',S,'W:',W)
