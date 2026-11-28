from heapq import heappush,heappop

INF=float('inf')
def dijkstra(n,e,s):
    N=[[] for _ in range(n)]
    for a,b,w in e:N[a].append((b,w))
    d=[INF]*n;d[s]=0; z=[(0,s)]
    while z:
        w,a=heappop(z)
        if d[a]!=w:continue
        for b,c in N[a]:
            v=w+c
            if v<d[b]:
                d[b]=v;heappush(z,(v,b))
    return d

def check(q,copies=1):
    s,t,a,b = [list(range(i*q,(i+1)*q)) for i in range(4)]
    h,cs,ct=4*q,4*q+1,4*q+2
    n=ct+1; E={(cs,ct,3)}; Q={}
    for i in range(q):
        E.update([(s[i],a[i],1),(b[i],t[i],1),(a[i],h,4),(h,b[i],4),
                  (a[i],b[i],8),(cs,b[i],1),(b[i],a[i],1),(a[i],ct,1)])
        for j in range(i+1,q):
            for h0 in range(copies):
                u,v=n,n+1;n+=2;Q[i,j,h0]=(u,v)
                E.update([(h,u,1),(u,h,1),(u,v,1),(v,u,1),(a[j],v,2),(v,b[i],2)])
    rev=lambda D:{(v,u,w) for u,v,w in D}
    Ds=[]
    for i,(x,y) in enumerate(zip(s+[cs],t+[ct])):
        dx=dijkstra(n,E,x); dy=dijkstra(n,rev(E),y)
        assert dx[y]==(10 if i<q else 3)
        Ds.append({(u,v,w) for u,v,w in E if dx[u]+w+dy[v]==dx[y]})
    U=set().union(*Ds)
    assert U==E
    fh=dijkstra(n,U,h); bh=dijkstra(n,rev(U),h)
    C={x for x in range(n) if max(fh[x],bh[x])<INF}
    assert C==set(a+b+[h]+[v for p in Q.values() for v in p])
    for i in range(q):
        Ed={e for e in Ds[i] if e[0] in C and e[1] in C}
        dx=dijkstra(n,Ed,a[i]);dy=dijkstra(n,rev(Ed),b[i])
        assert dx[b[i]]==8
        assert Ed=={(u,v,w) for u,v,w in Ed if dx[u]+w+dy[v]==8}
    for (i,j,_),(u,v) in Q.items():
        assert (u,v,1) in Ds[i] and (v,u,1) in Ds[j]
    P=[(s[i],a[i],b[i],t[i]) for i in range(q)]+[(cs,ct)]
    assert len(set(v for p in P for v in p))==sum(map(len,P))
    assert all(any(a==u and b==v for a,b,w in Ds[i]) for i,p in enumerate(P) for u,v in zip(p,p[1:]))
    support=[{p for e in D for p in e[:2]} for D in Ds[:q]]
    assert all(sum(v in V for V in support)==1 for v in a+b)
    assert all((b[i],a[i],1) in Ds[-1] for i in range(q))
    return n,len(C),len(Q)
for q in range(2,26): n,c,p=check(q)
print('24 exact families checked; largest n/SCC/pair conflicts:',n,c,p)

for copies in (2,8,32,128): n,c,p=check(5,copies)
print("4 inflated quota-zero families; largest n/SCC/pair conflicts:",n,c,p)
