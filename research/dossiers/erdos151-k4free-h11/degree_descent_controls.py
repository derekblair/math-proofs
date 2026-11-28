"""Exact small-graph tests of private-owner incidence implications."""
from itertools import combinations
from random import Random

def check(g,n):
    ax=range(n); tri=set();lone=[0]*n
    for i,j,k in combinations(ax,3):
        if g[i]>>j&1 and g[i]>>k&1 and g[j]>>k&1:
            if g[i]&g[j]&g[k]:return None
            tri.add((1<<i)|(1<<j)|(1<<k))
    for i,j in combinations(ax,2):
        if g[i]>>j&1 and not g[i]&g[j]:
            tri.add((1<<i)|(1<<j))
            lone[i]|=1<<j;lone[j]|=1<<i
    def free(s):return all(s&a!=a for a in tri)
    beta=max(s.bit_count() for s in range(1<<n) if free(s))
    L=0
    for i,S in enumerate(g):
        d=S.bit_count()
        k=beta-d
        if k not in (0,1,2):continue
        X=[u for u in ax if u!=i and not(S>>u&1)]
        U=[u for u in X if free(S|(1<<u))]
        U0=set(U)
        assert len(U)<=(0,3,8)[k]
        a=b=c=q=ell=edges=0
        for x in X:
            s=(g[x]&S).bit_count()
            l=(lone[x]&S).bit_count()
            edges+=s;ell+=l
            if x in U0:continue
            assert s>=1 and (s==1)==(s==1 and l==1)
            if s==1:a+=1
            if s==2:
                if l==0:b+=1
                elif l==1:c+=1
                else:q+=1
            for u in ax:
                if S>>u&1 and free((S^(1<<u))|(1<<x)):
                    assert g[x]>>u&1
        if k==0:
            assert a+b+c<=d
            assert 2*edges+3*d+ell>=6*len(X)
        if k==1:
            assert 5*a+4*b+5*c<=10*d
            assert 4*edges+10*d+3*ell>=12*(len(X)-len(U))
        if k==2 and ell==0:
            assert b<=4*d and edges+b>=3*(len(X)-len(U))
        L+=1
    return L
if __name__=='__main__':
    c0=c1=0
    for n in range(2,7):
        E=list(combinations(range(n),2))
        for mask in range(1<<len(E)):
            g=[0]*n
            for t,(i,j) in enumerate(E):
                if mask>>t&1:g[i]|=1<<j;g[j]|=1<<i
            x=check(g,n)
            if x is not None:c0+=1;c1+=x
    print(c0,'labeled K4-free graphs;',c1,'isolated local-score controls')
