from collections import deque

def dist(n, E, src):
    adj=[[] for _ in range(n)]
    for u,v in E:adj[u].append(v)
    D={src:0}; q=deque([src])
    while q:
        u=q.popleft()
        for v in adj[u]:
            if v not in D:
                D[v]=D[u]+1;q.append(v)
    return D

def check(q,L):
    s,a,b,t=[list(range(q*i,q*(i+1))) for i in range(4)]
    cs,ct,p,w=range(4*q,4*q+4)
    tracks=[list(range(w+1+L*i,w+1+L*(i+1))) for i in range(q)]
    n=tracks[-1][-1]+1
    E={(cs,p),(p,w),(w,ct)}
    for i in range(q): E.update(((s[i],a[i]),(b[i],t[i]),(cs,b[i]),(b[i],a[i]),(a[i],ct)))
    for z in tracks:
        E.update(zip(z,z[1:]))
        E.update((u,z[0]) for u in a)
        E.update((z[-1],v) for v in b)
    rev=lambda E: {(v,u) for u,v in E}
    def support(x,y):
        f=dist(n,E,x); g=dist(n,rev(E),y)
        return {(u,v) for u,v in E if f.get(u,n)+1+g.get(v,n)==f[y]},f[y]
    routes=[]
    for i in range(q):
        D,d=support(s[i],t[i])
        assert d==L+3 and D=={(s[i],a[i]),(b[i],t[i])}|set.union(*[
            set(zip(z,z[1:]))|{(a[i],z[0]),(z[-1],b[i])} for z in tracks])
        routes.append(D)
    DS,ds=support(cs,ct); assert ds==3
    U=set.union(DS,*routes)
    C=dist(n,U,a[0]).keys() & dist(n,rev(U),a[0]).keys()
    assert C==set(a+b).union(*map(set,tracks))
    lev={v:0 for v in a}|{v:L+1 for v in b}|{v:j for z in tracks for j,v in enumerate(z,1)}
    assert all(lev[v]-lev[u]<=1 for u,v in U if u in C and v in C)
    assert all(lev[v]-lev[u]==1 for D in routes for u,v in D if u in C and v in C)
    assert all(sum(v in {x for e in D for x in e} for D in routes)==q for z in tracks for v in z)
    return n,len(C),q*L

if __name__=='__main__':
    for q in range(2,10):
        for L in (1,2,3,6,16,64): out=check(q,L)
    print("48 track quota-lower fixtures; largest n/SCC/quota:",out)
