from itertools import product
from math import comb,lcm
from fractions import Fraction

def compatible(s,a,b):
    r,pa,j=a
    q,pb,k=b
    e=max(0,j+k-s)
    return any(e+r+q+i <= ((pa&((1<<i)-1)).bit_count()+(pb&((1<<i)-1)).bit_count())
               for i in range(min(j+k,s)+1))

def graph(s):
    V=tuple(a for a in product(range(s//2+1),range(1<<s),range(s+1))
           if (0 <= a[2]+a[0]-a[1].bit_count()) and compatible(s,a,a))
    adj=tuple(sum(1<<j for j,b in enumerate(V) if i!=j and compatible(s,a,b))
              for i,a in enumerate(V))
    return V,adj

def maximal(adj):
    def rec(P,X,R):
        if not (P|X):
            yield R; return
        Y=P|X
        best=None; score=-1
        while Y:
            y=Y&-Y; Y^=y
            ai=adj[y.bit_length()-1]
            w=(ai&P).bit_count()
            if w>score:best=ai;score=w
        Y=P&~best
        while Y:
            y=Y&-Y; Y^=y
            i=y.bit_length()-1
            A=adj[i]
            yield from rec(P&A,X&A,R+(i,))
            P^=y; X|=y
    yield from rec((1<<len(adj))-1,0,())

def binom(a,b):
    return comb(a,b) if 0<=b<=a else 0

def solve(t,u,s,weighted=True):
    V,A=graph(s)
    D=lcm(*(comb(t+u+s,t+j) for j in range(s+1))) if weighted else 1
    W=[binom(t,r)*binom(u,j+r-mask.bit_count())*(D//comb(t+u+s,t+j) if weighted else 1)
       for r,mask,j in V]
    val,I=max((sum(W[i] for i in I),I) for I in maximal(A))
    return Fraction(val,D),tuple(V[i] for i in I if W[i])

if __name__=='__main__':
    from time import monotonic
    from sys import argv
    for s in range(int(argv[1])+1):
        b=monotonic();V,A=graph(s)
        print(s,len(V),sum(1 for I in maximal(A)),monotonic()-b,flush=True)

def solve_factored(t,u,s):
    """Return k and a profile witness; raw Lubell optimum = k*t!*u!/(t+u+s)!.

    Retain the factorials symbolically. Work need not scale with t+u.
    """
    from math import prod
    V,A=graph(s)
    R=[prod(range(t+1,t+j+1))*prod(range(u+1,u+s-j+1)) for j in range(s+1)]
    W=[binom(t,r)*binom(u,j+r-mask.bit_count())*R[j] for r,mask,j in V]
    value,I=max((sum(W[i] for i in I),I) for I in maximal(A))
    return value,tuple(V[i] for i in I if W[i])
