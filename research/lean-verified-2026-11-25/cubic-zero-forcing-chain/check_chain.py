"""Independent integer graph/forcing/domination schedule check for the exact published chain."""
from collections import Counter
from itertools import combinations
from contextlib import redirect_stdout
from io import StringIO
with redirect_stdout(StringIO()):
    from interfaces import block
for k in range(2,61):
    ids=list(range(k))
    G={(i,u):{(i,v) for v in block(1+(0<i<k-1))[u]} for i in ids for u in range(7+(0<i<k-1))}
    for i in range(k-1):
        a=(i,6 if i==0 else 7); b=(i+1,6)
        G[a].add(b);G[b].add(a)
    assert len(G)==8*k-2 and all(len(N)==3 for N in G.values())
    assert not any(G[x]&G[y] for x,N in G.items() for y in N)
    S={(i,j) for i in ids for j in ([0,1,3,4] if i==0 else [0,1,4])}
    assert len(S)==3*k+1
    for i in ids:
        seq = [(1,5),(0,6),(3,2)] if i==0 else [(0,5),(1,3),(3,2)] if i==k-1 else [(0,5),(5,2),(2,3),(1,7)]
        pairs=[((i,x),(i,y)) for x,y in seq]
        if i<k-1:pairs.append(((i,6 if i==0 else 7),(i+1,6)))
        for x,y in pairs:
            assert x in S and G[x]-S=={y},(k,i,x,y)
            S.add(y)
    assert S == set(G)
    high={i for i in ids if i%3==(2 if k%3==2 else 1)}
    assert len(high)==k//3 and not ({0,k-1}&high)
    D={(i,j) for i in ids for j in ([2,6,7] if i in high else [1,4] if i-1 in high and 0<i<k-1 else [0,3])}
    assert len(D)==2*k+k//3
    assert all(x in D or N&D for x,N in G.items())
    # Independent exact domination transfer DP: enumerate each local D, keep current outgoing
    # port condition (0: needs cover; 1: internally covered; 2: chosen), total minimum.
    rows={1:0}
    for i in ids:
        L=block(1+(0<i<k-1)); m=len(L)
        opt={}
        for mask in range(1<<m):
            P={v for v in range(m) if mask>>v&1}
            C=P.union(*(L[j] for j in P))
            if not set(range(6))<=C:continue
            cond=lambda w:2 if w in P else 1 if w in C else 0
            a=1 if i==0 else cond(6)
            b=1 if i==k-1 else cond(6 if i==0 else 7)
            for prev,c in rows.items():
                if (prev==0 and a!=2) or (a==0 and prev!=2):continue
                opt[b]=min(opt.get(b,10*k),c+len(P))
        rows=opt
    assert rows[1]==len(D)
print("Exact source-shaped chains k=2..60: verify order/cubic/triangle-free, valid 3k+1 forcing, valid + DP-optimal 2k+floor(k/3) domination")
