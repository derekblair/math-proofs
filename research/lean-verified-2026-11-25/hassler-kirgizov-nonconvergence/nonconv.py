from itertools import product
from fractions import Fraction
A=((2,3,1),(3,1,2))
B=((2,3,1),(3,2,1))
q=(2,3,1,5,6,4,8,9,7)
W=9
def patt(seq):
    ix={v:i for i,v in enumerate(sorted(seq),1)}
    return tuple(ix[v] for v in seq)
def wrap(n, family, complement):
    out=set()
    for i in range(3):
        j=(n-i)%3
        L=tuple({patt(m[-i:]) for m in family}) if i else ((),)
        R=tuple({patt(m[:j]) for m in family}) if j else ((),)
        for arr in product(L,*([family]*((n-i)//3)),R):
            seq=[];base=0
            for block in arr:
                seq.extend(base+x for x in block)
                base+=len(block)
            if complement:seq=[n+1-x for x in seq]
            out.add(tuple(seq))
    return out
allow=wrap(W,A,False)|wrap(W,B,True)
s=allow
for n in range(W,20):
    a,b=wrap(n,A,False),wrap(n,B,True)
    assert not a&b and s==a|b,(n,len(a),len(b),len(s))
    t=sum(sum(patt(seq[i:i+W])==q for i in range(n-W+1)) for seq in s)
    k,r=divmod(n,3)
    m=n-W
    h,j=divmod(m,3)
    assert len(s)==(44,56,72)[j]*2**h
    assert t==((3*h+1),(4*h+2),5*(h+1))[j]*2**h
    f=Fraction(t,n*len(s))
    lim=(Fraction(6,11),Fraction(4,7),Fraction(5,9))[r]/24
    print(n,len(a),len(b),len(s),t,str(f),float(lim),flush=True)
    rem=set()
    for p in s:
        for r in range(1,n+2):
            tup=tuple(x+(x>=r) for x in p)+(r,)
            if patt(tup[-W:]) in allow:rem.add(tup)
    s=rem
