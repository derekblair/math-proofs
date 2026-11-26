from itertools import combinations
from functools import lru_cache
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
import json

def norm(v):
    v=tuple(v)
    return tuple(-x for x in v) if next((x for x in v if x),1)<0 else v
def neg(v):return tuple(-x for x in v)
def sub(v,w):return tuple(x-y for x,y in zip(v,w))
def compute(N,adj,ch,ws):
    D={(u,v):0 for u in range(N) for v in adj[u]}; m=len(ch)
    for j,(u,v) in enumerate(ch,1):D[u,v]=j;D[v,u]=-j
    rows={}
    for s in ws:
        z=[0]*m;pre={}
        C=set()
        for i,u in enumerate(s):
            for h in pre.get(u,[]):C.add(norm(sub(z,h)))
            pre.setdefault(u,[]).append(z.copy())
            v=s[(i+1)%len(s)];k=D[u,v]
            if k:z[abs(k)-1]+=1 if k>0 else -1
        if (0,)*m in C:continue
        rows.setdefault((norm(z),tuple(sorted(C))),s)
    return {a:rows[a] for a in sorted(rows,key=lambda a:(len(a[1]),sum(map(abs,a[0]))))},m
def step_graph(n,k):
    N=2*n; adj=[set() for i in range(N)]
    def add(u,v):adj[u].add(v);adj[v].add(u)
    for i in range(n):add(i,(i+1)%n);add(i+n,(i+k)%n+n);add(i,i+n)
    return N,adj
def tc():
    N=30;adj=[set() for i in range(N)]
    P=list(combinations(range(6),2))
    def match(u):
        if not u:yield [];return
        for j in u[1:]:
            for M in match([x for x in u[1:] if x!=j]):yield [(u[0],j)]+M
    for j,M in enumerate(match(list(range(6))),15):
        for x in M:
            i=P.index(x);adj[i].add(j);adj[j].add(i)
    return N,adj
def gauge(N,adj):
    seen={0};s=[0];T=set()
    for u in s:
        for v in sorted(adj[u]):
            if v not in seen:
                seen.add(v);s.append(v);T.add(tuple(sorted((u,v))))
    return [(u,v) for u in range(N) for v in sorted(adj[u]) if u<v and (u,v) not in T]
def words(N,adj,lengths):
    L=max(lengths)
    for u in range(N):
        path=[u]
        def visit():
            w=path[-1];size=len(path)
            if size in lengths and u in adj[w] and path[-2]!=u and path[1]<w:
                yield tuple(path)
            if size==L:return
            for v in sorted(adj[w]):
                if v>=u and (size==1 or v!=path[-2]):
                    path.append(v);yield from visit();path.pop()
        yield from visit()
def search(rows,d):
    count=0
    used=set()
    @lru_cache(None)
    def basis(vs):
        if not vs:return ()
        Q=hermite_normal_form(Matrix(vs).T)
        return tuple(tuple(Q[:,j]) for j in range(Q.cols))
    @lru_cache(None)
    def check(g):
        nonlocal count
        count+=1
        piv=[max(j for j,x in enumerate(v) if x) for v in g]
        assert piv==sorted(set(piv))
        def member(v):
            a=list(v)
            for i,p in reversed(list(enumerate(piv))):
                s,t=divmod(a[p],g[i][p])
                if t:return False
                if s:
                    for j in range(p+1):a[j]-=s*g[i][j]
            return not any(a)
        for z,C in rows:
            if member(z) and not any(map(member,C)):
                used.add((z,C))
                for c in C:
                    s=check(basis(g+(c,)))
                    if s is not None:return s
                return None
        return g
    ans=check(())
    return ans,count,used
def run(name,N,A,ch,W):
    R,d=compute(N,A,ch,W)
    result,states,_=search(R,d)
    print(name,'rank',d,'rows',len(R),'states',states,'bad exists',result is not None,flush=True)

if __name__=='__main__':
    for n,k in [(5,2),(4,1),(8,3),(10,2)]:
        N,A=step_graph(n,k); G=gauge(N,A)
        run(f'G({n},{k}) up to 16',N,A,G,words(N,A,{4,8,16}))
