from itertools import combinations, product
from collections import Counter
from random import Random
from math import ceil
from functools import reduce
from operator import xor

def xsum(values):return reduce(xor,values,0)

def witnesses(n,r,d,J):
    v=[0]*n
    for i,j in enumerate(J):
        v[j]^=1<<i
        v[d]^=1<<i
    return v

count=0
for n,r in [(4,3),(6,3),(8,4)]:
    for d in (0,n-1):
        hist=Counter()
        for J in product(range(n),repeat=r):
            v=witnesses(n,r,d,J)
            assert xsum(v)==0
            hist[tuple(v)]+=1
        assert len(hist)==n**r and set(hist.values())=={1}
        for A in combinations(range(n),n//2):
            h=Counter(xsum(v[a] for a in A) for v in hist)
            assert len(h)==1<<r and set(h.values())=={(n//2)**r}
            count+=1

def mul(a,b):
    out=0
    while b:
        if b&1:out ^= a
        b>>=1;a<<=1
        if a&8:a^=11
    return out
def prod8(xs):return reduce(mul,xs,1)
def ev(P,a):
    y=0
    for c in reversed(P):y=mul(y,a)^c
    return y

S=(1,2,3,4);n=len(S);r=3
V=[witnesses(n,r,0,J) for J in product(range(n),repeat=r)]
D=[prod8(a^b for b in S if b!=a) for a in S]
refresh=[[prod8((a,d,x)) for a,d,x in zip(S,D,v)] for v in V]
# Verify interpolation's leading cancellation and all site evaluations.
for i,v in enumerate(V):
    W=[0]*n
    for a,w in zip(S,v):
        H=[1]
        for b in S:
            if b==a:continue
            H=[mul(b,H[0])]+[H[j-1]^mul(b,H[j]) for j in range(1,len(H))]+[H[-1]]
        W=[x^mul(w,y) for x,y in zip(W,H)]
    assert W[-1]==0
    assert [mul(a,ev(W,a)) for a in S]==refresh[i]
initial=[tuple(ev((0,)+c,a) for a in S) for c in product(range(8),repeat=3)]
views=0
for B in combinations(range(n),n//2):
    hist=Counter(tuple(x^(w[i] if i in B else 0) for i,x in enumerate(u))
                 for u in initial for w in refresh)
    # Full mask distribution is uniform over all 8^4 possible views;
    # hence the fused transcript is independent of every field secret.
    assert len(hist)==8**4 and set(hist.values())=={8}
    views+=1

rng=Random(11)
collisions=0
for m,r in [(4,4),(6,4),(8,5),(10,5),(12,5)]:
    k=ceil(m/r)
    if m==12:continue # keep subset catalogs small
    masks=list(combinations(range(2*m),m))
    for _ in range(30):
        X=[]
        for _ in range(k):
            v=[rng.randrange(1<<r) for _ in range(2*m-1)]
            v.append(xsum(v))
            assert xsum(v)==0
            X.append(v)
        assert any(len({xsum(v[j] for j in A) for v in X})==1 for A in masks)
        collisions+=1
print(count,'exact balanced-syndrome distributions;',views,'full affine view distributions;',
      collisions,'direct simultaneous collision controls')

# Nontrivially correlated exact pair: antisymmetric probability flow on
# a cycle, added to the independent law. Integer weights out of n^2.
from math import comb, factorial
for n in (4,6,8,12):
    P={(i,j):1+int(j==(i+1)%n)-int(j==(i-1)%n)
       for i,j in product(range(n),repeat=2)}
    assert any(p==0 for p in P.values())
    assert sum(P[i,i] for i in range(n))==n
    for A in map(set,combinations(range(n),n//2)):
        h=Counter()
        for (i,j),p in P.items():h[(i in A,j in A)]+=p
        assert len(h)==4 and set(h.values())=={n*n//4}
    for t in range(1,n//4+1):
        # Integer recurrence constant bound used in the induction.
        assert sum(comb(t,s)**2 * 4**(t-s)*factorial(t-s)**2 *
                   (2**s)*factorial(s) for s in range(1,t+1,2)) <= 4**t*factorial(t)**2
print('4 nonuniform pair couplings and induction constants verified')
