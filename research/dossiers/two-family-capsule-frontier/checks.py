"""Offline finite multiplicity and independent-sharing comparisons only."""
from itertools import product, combinations
from collections import Counter

def uniform_opt(n,c,f):
    a=c+f+1
    if n>=2*a: return 2*a
    if n>=a+f:return 2*(a+f)
    return None

def exhaustive():
    checked=0
    for n in range(1,6):
        ans={(c,f):None for c in range(n) for f in range(n)}
        for W in product(range(3),repeat=2*n):
            U,V=W[:n],W[n:]
            e1,e2=sum(U),sum(V)
            q1=sorted(U,reverse=True)
            q2=sorted(V,reverse=True)
            L=sorted((u+v for u,v in zip(U,V)),reverse=True)
            z0,z1,z2=0,0,0
            m=e1+e2
            for c in range(n):
                if c: z1+=q1[c-1]; z2+=q2[c-1]
                z0=0
                for f in range(n):
                    if f: z0+=L[f-1]
                    via_cut=e1>=z1+z0+1 and e2>=z2+z0+1
                    via_threshold=max(e2+z1,e1+z2)+1<=m-z0
                    assert via_cut==via_threshold
                    if via_cut:
                        pred=uniform_opt(n,c,f)
                        assert pred is not None and m>=pred
                        if ans[c,f] is None or ans[c,f]>m: ans[c,f]=m
                    checked+=1
        for (c,f),v in ans.items():
            assert v==uniform_opt(n,c,f)
    return checked

def offset_check():
    Q=5
    xys=list(product(range(Q),repeat=3))
    patterns=0
    for broken in (0,1):
        for compromised in ((),(0,),(1,),(2,)):
            states=[]
            for secret in range(Q):
                d=Counter()
                for r,u,v in xys:
                    shares=(tuple((r+x*u)%Q for x in (1,2,3)),
                            tuple((secret-r+x*v)%Q for x in (1,2,3)))
                    d[shares[broken],tuple(shares[1-broken][k] for k in compromised)]+=1
                    for i,j in combinations(range(3),2):
                        x,x1=i+1,j+1
                        Z=[(x1*Qf[i]-x*Qf[j])*pow(x1-x,-1,Q)%Q for Qf in shares]
                        assert sum(Z)%Q==secret
                states.append(d)
            assert all(d==states[0] for d in states)
            patterns+=1
    return patterns

if __name__=='__main__':
    print(exhaustive(),'weighted-layout comparisons; exact closed-form uniform optimum agrees.')
    print(offset_check(),'GF5 disclosure patterns across every secret, offset and sharing mask.')
