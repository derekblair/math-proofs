"""Exhaustive synthetic adaptive checks over GF(5), not repair software."""
from collections import Counter
from itertools import product

Q=5
P=list(product(range(Q),repeat=3))
Z=[x for x in P if not x[0]]

def add(x,y): return tuple((a+b)%Q for a,b in zip(x,y))
def minus(x,y): return tuple((a-b)%Q for a,b in zip(x,y))
def ev(p,a): return sum(c*a**i for i,c in enumerate(p))%Q
def clear(p,a): return minus(p,(ev(p,a),0,0))

def wire(p,a):
    hs=[x for x in range(1,Q) if x!=a]
    out=[]
    for h in hs:
        w=1
        for v in hs:
            if v!=h: w=w*(a-v)*pow((h-v)%Q,-1,Q)%Q
        out.append(w*ev(p,h)%Q)
    return tuple(out)

def execute(p, R, seed, simulated):
    out=[]
    for e,r in enumerate(R):
        # Only the previous message is used by this synthetic policy.
        a=1 if e==0 else 1+out[-1][2][0]%4
        f=add(p,r)
        y=ev(f,a)
        if simulated:
            w=wire(add((y,0,0),clear(seed,a)),a)
        else:
            pad=clear(minus(seed,r),a)
            assert ev(pad,a)==0
            w=wire(add(f,pad),a)
        assert sum(w)%Q==y
        out.append((a,y,w))
    return tuple(out)

def main():
    histories=0
    for p in P:
        for r,s in product(Z[::4],repeat=2):
            R=[(0,0,0),r,add(r,s)]
            real=Counter(execute(p,R,k,False) for k in Z)
            sim=Counter(execute(p,R,k,True) for k in Z)
            assert real==sim
            assert len(real)==len(Z)
            histories+=1
    K={wire(clear(z,1),1) for z in Z}
    assert len(K)==25 and all(sum(x)%Q==0 for x in K)
    # Full translation invariance forces all 25 pads: every nonempty
    # proper linear subspace fails at least one required translate.
    for z in Z[1:]:
        line={wire(clear(tuple(k*x%Q for x in z),1),1) for k in range(Q)}
        assert len(line)==5
        assert any({add(x,v) for x in line}!=line for v in K)
    print(histories,'complete adaptive fixed true histories; 25 seeds each; exact laws agree.')
    print('All 24 nonzero pad directions fail to provide invariance when used alone.')
if __name__=='__main__': main()
