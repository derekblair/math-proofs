from itertools import product,combinations
from collections import Counter
from math import comb
from fractions import Fraction
from hashlib import sha256

# Set-based construction and maximal search independent of the bitset
# implementation. Lexicographically augment only when no earlier vertex
# already extends that same pivot branch.
def all_maximal(neighbors):
    def visit(R,P,X):
        if not P and not X:
            yield tuple(sorted(R));return
        pool=P|X
        pivot=min(pool,key=lambda x:(-len(P&neighbors[x]),-x))
        for v in sorted(P-neighbors[pivot],reverse=True):
            yield from visit(R+(v,),P&neighbors[v],X&neighbors[v])
            P.remove(v);X.add(v)
    yield from visit((),set(range(len(neighbors))),set())
def by_sets(s):
    def ok(A,B):
        r,I,j=A;q,J,k=B
        m=max(0,j+k-s)
        return any(i+r+q+m<=sum(z<i for z in I)+sum(z<i for z in J)
                   for i in range(s+1))
    V=[]
    for r in range(s//2+1):
        for mask in range(2**s):
            I={z for z in range(s) if (mask>>z)&1}
            for j in range(s+1):
                Q=(r,I,j)
                if j+r>=len(I) and ok(Q,Q):V.append(Q)
    N=[set() for _ in V]
    for i,j in combinations(range(len(V)),2):
        if ok(V[i],V[j]): N[i].add(j);N[j].add(i)
    C=sorted(all_maximal(N))
    return V,C

def standard_extra(k,slack):
    assert slack>=0
    return [comb(k,j) if 2*j<=slack else comb(k-1,j-1)
              if slack%2 and j==slack//2+1 else 0 for j in range(slack+1)]
def layers(t,u,s,low):
    if low: counts=standard_extra(u+s,s)
    else:
        right=standard_extra(u+s-2,s-2)
        counts=[0]+[sum(x * (right[j-i] if 0<=j-i<len(right) else 0)
                       for i,x in enumerate((t+2,1))) for j in range(s)]
    return counts

def score(t,u,s,low):
    return sum(Fraction(v,comb(t+u+s,t+j)) for j,v in enumerate(layers(t,u,s,low)))
def raw(t,u,s):
    n=t+u+s
    V=[a for a in range(1<<n) if t<=a.bit_count()<=t+s]
    N=[set() for _ in V]
    for i,j in combinations(range(len(V)),2):
        if (V[i]&V[j]).bit_count()>=t and (V[i]|V[j]).bit_count()<=t+s:
            N[i].add(j);N[j].add(i)
    W=[Fraction(1,comb(n,a.bit_count())) for a in V]
    return max(sum(W[i] for i in I) for I in all_maximal(N))

if __name__=='__main__':
    import quotient
    for s,p in [(4,5),(5,29),(6,191),(7,6865)]:
        A,C=by_sets(s)
        B,N=quotient.graph(s)
        D=tuple(quotient.maximal(N))
        assert [ (r,sum(1<<x for x in I),j) for r,I,j in A]==list(B)
        assert len(C)==len(set(C)) and C==sorted(tuple(sorted(x)) for x in D)
        for t,u in [(1,2),(2,2),(2,3),(2,12),(3,5),(3,6),(23,77),(47,47)]:
            def Q(i):
                v=Fraction(0)
                for r,I,j in (A[x] for x in D[i]):
                    z=j+r-len(I)
                    if r<=t and z<=u:
                        v+=Fraction(comb(t,r)*comb(u,z),comb(t+u+s,t+j))
                return v
            assert Q(0)==score(t,u,s,True) and Q(p)==score(t,u,s,False)
        # Degree ≤ floor(s/2) for each layer polynomial in t,u.
        d=s//2
        for t,u in product(range(1,d+2),range(2,d+3)):
            for k,lo in [(0,True),(p,False)]:
                profile_count=[0]*(s+1)
                for r,I,j in (A[x] for x in D[k]):
                    z=j+r-len(I)
                    assert 0<=z and r+z<=d
                    profile_count[j]+=comb(t,r)*comb(u,z)
                assert profile_count==layers(t,u,s,lo)
        print(s,len(A),len(C),sha256(repr(C).encode()).hexdigest(),flush=True)
    for t,u,s in [(1,2,4),(2,2,4)]:
        a=raw(t,u,s);b=quotient.solve(t,u,s)[0]
        assert a==b,(t,u,s,a,b)
        print('original',t,u,s,a,flush=True)
