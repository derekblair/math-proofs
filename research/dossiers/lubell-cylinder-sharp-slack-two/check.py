"""Independently maximize weighted cliques in the ORIGINAL (unshifted) set graph."""
from fractions import Fraction as Q
from math import comb, lcm

def optimum(n, t, u):
    vertices = [a for a in range(1<<n) if t<=a.bit_count()<=n-u]
    m = len(vertices)
    denom = lcm(*(comb(n,a.bit_count()) for a in vertices))
    cost = [denom//comb(n,a.bit_count()) for a in vertices]
    nbr = [0]*m
    for i,a in enumerate(vertices):
        for j,b in enumerate(vertices[:i]):
            if (a&b).bit_count()>=t and (a|b).bit_count()<=n-u:
                nbr[i]|=1<<j
                nbr[j]|=1<<i
    # Enumerate all maximal cliques by standard pivoted Bron–Kerbosch.
    # Every vertex has positive weight, so a maximum is among them.
    best=calls=0
    def search(P,X,value):
        nonlocal best,calls
        calls+=1
        if not P:
            if not X: best=max(best,value)
            return
        ux=P|X
        k=-1;count=-1
        while ux:
            b=ux&-ux;u=b.bit_length()-1;ux^=b
            d=(nbr[u]&P).bit_count()
            if d>count: k,count=u,d
        bset=P&~nbr[k]
        while bset:
            bit=bset&-bset;i=bit.bit_length()-1;bset^=bit
            search(P&nbr[i],X&nbr[i],value+cost[i])
            P^=bit
            X|=bit
    search((1<<m)-1,0,0)
    return Q(best,denom),calls

count = 0
for s in range(2,7):
    n=s+2
    for t in range(1,s):
        u=s-t
        v, calls=optimum(n,t,u)
        w=min(t,u); b=max(t,u)
        low=Q(1,comb(n,w))+Q(b+2,comb(n,w+1))
        cyl=Q(1,comb(n,w))+Q(2,comb(n,w+1))+Q(1,comb(n,w+2))
        assert v==max(low,cyl),(n,t,u,v)
        if b>=2: assert low>cyl
        print(n,t,u,v,calls)
        count+=1
assert count==15
