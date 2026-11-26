from collections import deque
from itertools import product,combinations
from math import inf
from random import Random

def adj(n,E,rev=False):
    A=[[] for _ in range(n)]
    for u,v in E:
        if rev:u,v=v,u
        A[u].append(v)
    return A

def search(A,s):
    prev={s:-1}; q=[s]
    for u in q:
        for v in A[u]:
            if v not in prev:prev[v]=u; q.append(v)
    return prev

def recover(prev,s,t):
    p=[]
    while t!=s:
        p.append((prev[t],t));t=prev[t]
    return p[::-1]

def strong(n,E):
    return all(len(search(adj(n,E,r),0))==n for r in (0,1))

def topo(A):
    deg=[0]*len(A)
    for vs in A:
        for v in vs:deg[v]+=1
    Q=[u for u,x in enumerate(deg) if x==0]
    for u in Q:
        for v in A[u]:
            deg[v]-=1
            if deg[v]==0:Q.append(v)
    return Q

def relax(A, order, seeds, w, rev=False):
    D=[inf]*len(A);P=[-1]*len(A)
    for u,b in seeds:D[u]=b
    for u in order:
        for v in A[u]:
            val=D[u]+w[(v,u) if rev else (u,v)]
            if val<D[v]:D[v]=val;P[v]=u
    return D,P

def back(P,t):
    p=[]
    while P[t]>=0:
        p.append((P[t],t));t=P[t]
    return p[::-1],t

def union_paths(n,E,w,a=0,b=1): # original graph with split terminals
    T={a,b}
    new=lambda u: u+n if u in T else u
    NE={(u,new(v)):(u,v) for u,v in E}
    W={e:w[v] for e,v in NE.items()}
    A=adj(2*n,NE);R=adj(2*n,NE,1);O=topo(A)
    assert len(O)==len(A)
    D1,P1=relax(A,O,[(a,0)],W)
    D2,P2=relax(A,O,[(b,0)],W)
    T1,S1=relax(R,O[::-1],[(new(b),0)],W,True)
    T2,S2=relax(R,O[::-1],[(new(a),0)],W,True)
    seeds=[(u,D1[u]+D2[u]) for u in range(n) if u not in T]
    J,I=relax(A,O,seeds,W)
    v=min((u for u in range(n) if u not in T),key=lambda u:J[u]+T1[u]+T2[u],default=-1)
    U=D1[new(b)]+D2[new(a)]
    if v==-1 or U<=J[v]+T1[v]+T2[v]:
        assert U<inf
        WIT=set(back(P1,new(b))[0]+back(P2,new(a))[0])
    else:
        U=J[v]+T1[v]+T2[v]
        middle,u=back(I,v)
        end1=back(S1,v)[0]
        end2=back(S2,v)[0]
        WIT=set(back(P1,u)[0]+back(P2,u)[0]+middle+[(i,j) for j,i in end1+end2])
    assert sum(W[e] for e in WIT)==U
    return U,{NE[e] for e in WIT}

def minimal(n, E, a=0, b=1):
    E=set(E)
    p=recover(search(adj(n,E),a),a,b)
    q=recover(search(adj(n,E),b),b,a)
    pv=[a]+[v for u,v in p]; qv=[b]+[v for u,v in q]
    C=set(pv[1:-1])&set(qv[1:-1])
    if C:
        first=next(v for v in pv if v in C)
        last=next(v for v in pv[::-1] if v in C)
        i,j=pv.index(first),pv.index(last)
        k,l=qv.index(first),qv.index(last)
        assert k<=l
        q=q[:k]+p[i:j]+q[l:]
    B=set(p+q)
    H=set(E)
    out=[0]*n; inc=[0]*n
    for u,v in H:out[u]+=1;inc[v]+=1
    for e in sorted(H-B):
        u,v=e
        if out[u]>1 and inc[v]>1:
            H.remove(e); out[u]-=1; inc[v]-=1
    assert strong(n,H)
    M=H-B; cand=set()
    for rev in (0,1):
        F=adj(n,M,rev); K=adj(n,B,rev)
        for u in range(n):
            if not F[u]:
                vs=K[u]; v=min(vs)
                e=(v,u) if rev else (u,v)
                if len(vs)>1:cand.add(e)
                else:M.add(e)
    cand-=M
    assert len(cand)<=2
    M|=cand
    _,U=union_paths(n,H,{e:int(e not in M) for e in H},a,b)
    H=M|U
    assert strong(n,H)
    for e in cand:
        if strong(n,H-{e}):H.remove(e)
    return H

def paths(A,s,t,forbid):
    if s==t:return [set()]
    return [{(s,u)}|p for u in A[s] if u not in forbid for p in paths(A,u,t,forbid)]

def main():
    rng=Random(29372); tested=0; dp=0
    for n in range(2,6):
        cand=[(u,v) for u in range(n) for v in range(n) if u!=v and (u<2 or v<2 or u<v)]
        cases=(range(1<<len(cand)) if n<=4 else (rng.randrange(1<<len(cand)) for _ in range(5000)))
        for mask in cases:
            E={e for i,e in enumerate(cand) if mask>>i&1}
            if not strong(n,E):continue
            O=minimal(n,E)
            assert strong(n,O) and O<=E and not any(strong(n,O-{e}) for e in O)
            tested+=1
            w={e:rng.randrange(10) for e in E}
            V,_=union_paths(n,E,w)
            A=adj(n,E)
            chk=min(sum(w[e] for e in x|y) for x,y in product(paths(A,0,1,{0}),paths(A,1,0,{1})))
            assert V==chk;dp+=1
    for n in range(6,35):
      cand=[(u,v) for u in range(n) for v in range(n) if u!=v and (u<2 or v<2 or u<v)]
      for _ in range(200):
        E={e for e in cand if rng.random()<.19}
        # Include a random-position directed cycle so every sample is strongly connected.
        iv=list(range(2,n));cut=rng.randrange(len(iv)+1)
        Q=[0]+iv[:cut]+[1]+iv[cut:]+[0]
        E.update(zip(Q,Q[1:]))
        O=minimal(n,E)
        assert strong(n,O) and O<=E and not any(strong(n,O-{e}) for e in O)
        tested+=1
    print(tested,'exact inclusion-minimal strong certificates;',dp,'exhaustive two-path union comparisons')
if __name__=='__main__':main()
