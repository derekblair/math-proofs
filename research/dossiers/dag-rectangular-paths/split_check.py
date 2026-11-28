from random import Random
from itertools import product
from heapq import heappop,heappush
INF=10**9

def dist(n,A,s):
    N=[[] for _ in range(n)]
    for (u,v),w in A.items():N[u].append((v,w))
    D=[INF]*n;D[s]=0;heap=[(0,s)]
    while heap:
        d,u=heappop(heap)
        if d!=D[u]:continue
        for v,w in N[u]:
            z=d+w
            if z<D[v]:D[v]=z;heappush(heap,(z,v))
    return D,N
def allshort(n,A,s,t):
    D,N=dist(n,A,s)
    def go(u,P):
        if u==t:return [P]
        return [Q for v,w in N[u] if D[v]==D[u]+w for Q in go(v,P+(v,))]
    return D[t],go(s,(s,)) if D[t]<INF else []
def states(options):
    def go(i,occ,out):
        if i==len(options):return out
        for p in options[i]:
            vertices=set(p)
            if not occ&vertices:
                r=go(i+1,occ|vertices,out+(p,))
                if r is not None:return r
        return None
    return go(0,set(),())

def test(n,A,ST,F,counters):
    original=[allshort(n,A,s,t) for s,t in ST]
    target=states([p for _,p in original])
    reserved={s for s,t in ST if s==t}
    U={e:A[e] for _,p in original for v in p for e in zip(v,v[1:]) if not reserved.intersection(e)}
    k=len(ST); clone_ids={v:n+i for i,v in enumerate(sorted(F))}
    out=lambda v:v
    inc=lambda v:clone_ids.get(v,v)
    C={(out(u),inc(v)):w for (u,v),w in U.items()}
    N=n+len(F)
    # Check actual structural DAG and one representative per directed edge.
    indeg=[0]*N; adj=[[] for _ in range(N)]
    for a,b in C:indeg[b]+=1;adj[a].append(b)
    q=[a for a in range(N) if indeg[a]==0]; used=0
    for a in q:
        used+=1
        for b in adj[a]:
            indeg[b]-=1
            if indeg[b]==0:q.append(b)
    assert used==N and len(U)==len(C)
    assert all(not any(y==v for _,y in C) and not adj[inc(v)] for v in F)
    terminals={u for P in ST for u in P}
    nonterm=sorted(F-terminals); answer=None
    old_d=[dist(n,A,s)[0] for s,t in ST]
    for B in product(range(-1,k),repeat=len(nonterm)):
        counters[0]+=1
        pairs=[]; frag_owner=[]; valid=True
        for i,(s,t) in enumerate(ST):
            S=sorted((v for v,o in zip(nonterm,B) if o==i),key=lambda v:old_d[i][v])
            if s==t:
                if S:valid=False
                continue
            V=[s]+S+[t]
            if any(old_d[i][v]<=old_d[i][u] for u,v in zip(V,V[1:])):valid=False;break
            pairs += [(out(u),inc(v)) for u,v in zip(V,V[1:])]
            frag_owner += [i]*(len(V)-1)
        if not valid:continue
        choices=[allshort(N,C,s,t) for s,t in pairs]
        if any(p==[] for _,p in choices):continue
        totals=[0]*k
        for i,(d,_) in zip(frag_owner,choices):totals[i]+=d
        if totals!=[d for d,_ in original]:continue
        actual=states([p for _,p in choices])
        if actual is None:continue
        P=[[] if s!=t else [s] for s,t in ST]
        for p,i in zip(actual,frag_owner):
            p=[v if v<n else sorted(F)[v-n] for v in p]
            if P[i]:assert P[i][-1]==p[0];P[i].extend(p[1:])
            else:P[i].extend(p)
        for i,p in enumerate(P):
            assert tuple(p) in original[i][1]
        assert len(set(v for p in P for v in p))==sum(map(len,P))
        answer=P
        counters[1]+=1
        counters[2]+=sum(u in F and v in F for p in P for u,v in zip(p,p[1:]))
        counters[3]+=sum(v in terminals for v in F)
        # Continue to check every apparently feasible branch, not just the first.
    assert (answer is not None)==(target is not None)

if __name__=='__main__':
    rng=Random(12); counters=[0,0,0,0]
    for _ in range(320):
        n=9;k=3;F=set(rng.sample(range(n),rng.randrange(4)))
        A={(u,v):rng.randrange(1,7) for u in range(n) for v in range(n)
           if u!=v and (u<v or u in F or v in F) and rng.randrange(4)==0}
        T=rng.sample(range(n),2*k)
        ST=list(zip(T[:k],T[k:]))
        if _%7==0:ST[0]=(T[0],T[0])
        test(n,A,ST,F,counters)
    # Forced F→F same-label transition survives exclusively as plus-to-minus.
    test(9,{(0,7):2,(7,6):1,(6,3):2,(1,4):1,(2,5):1},[(0,3),(1,4),(2,5)],{6,7},counters)
    for _ in range(120):
        n=12
        A={(0,9):1,(9,8):1,(8,3):1,(1,7):1,(7,4):1,(2,10):1,(10,5):1}
        F={7,8,9,10}
        if _%3==0:F.add(0)
        if _%5==0:F.add(5)
        for u in range(n):
            for v in range(n):
                if u!=v and (u<v or u in F or v in F) and rng.randrange(5)==0:
                    A.setdefault((u,v),rng.randrange(8,20))
        test(n,A,[(0,3),(1,4),(2,5)],F,counters)
    assert counters[2] and counters[3]
    print('441 exact graph checks; branches, valid witnesses, F→F joins, feedback terminals:',*counters)
