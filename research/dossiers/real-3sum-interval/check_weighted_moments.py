"""Independent tiny exact control for the all-six-coordinate contraction."""
from itertools import product
from collections import Counter, defaultdict
from random import Random

def minus(a,b): return (a[0]-b[0],a[1]-b[1])
def plus(a,b): return (a[0]+b[0],a[1]+b[1])
def ancestors(num, side, bits):
    return [(b,num>>(b+1)) for b in range(bits) if (num>>b)&1==side]

def incidence(A,B,I,r,s,weak):
    d=len(A[0]); side=[]
    for who,R in enumerate((A,B)):
        inv=defaultdict(Counter)
        for i,X in enumerate(R):
            for p in range(d):
                for a in I if who==0 else range(d):
                    t0=r[minus(X[a],X[p])] if who==0 else r[minus(X[p],X[a])]+weak
                    for others in product(range(d),repeat=s):
                        t=[t0]
                        for z in others:
                            t.append(r[minus(X[z],X[a])] if who==0 else r[minus(X[a],X[z])]+1)
                        for key in product(*(ancestors(x,who,(len(r)+1).bit_length()) for x in t)):
                            inv[key][i,p]+=1
        side.append(inv)
    return side

def verify():
    rng=Random(62409); count=0
    for d in (2,3,4):
      for sample in range(10):
        m=2
        A=[sorted((rng.randrange(3),i*d+k+1) for k in range(d)) for i in range(m)]
        B=[sorted((rng.randrange(3),(i*d+k+1)*(m*d+1)) for k in range(d)) for i in range(m)]
        r={v:i for i,v in enumerate(sorted({minus(x,y) for R in (A,B) for X in R for x in X for y in X}))}
        for I,s,weak in product([range(d),range(d//2,d)],range(3),range(2)):
            lft,rgt=incidence(A,B,I,r,s,weak)
            for j,i,q,p in product(range(m),range(m),range(d),range(d)):
                acc=small=0
                for key,L in lft.items():
                    R=rgt.get(key,Counter())
                    term=L[i,p]*R[j,q]
                    if len(R)<=sample%5+1: small+=term
                    else: acc+=term
                sums={(k,l):plus(A[i][k],B[j][l]) for k,l in product(range(d),repeat=2)}
                rank={z:idx+1 for idx,z in enumerate(sorted(sums.values()))}
                pred=(lambda x,y:x<=y) if weak else (lambda x,y:x<y)
                want=sum(rank[sums[k,l]]**s for k,l in product(I,range(d)) if pred(sums[k,l],sums[p,q]))
                assert acc+small==want
                count+=1
    print('pointwise degree-split weighted contraction controls:',count)
if __name__=='__main__': verify()
