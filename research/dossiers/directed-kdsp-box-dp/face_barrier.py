from fractions import Fraction as Q
import heapq

def check(k):
    a = (k-1)//2
    J = range(a)
    I = range(a,k-1)
    graph = {}
    z, r = {}, {}
    def edge(u,v,w):
        assert w>0
        graph.setdefault(u,[]).append((v,w))
        graph.setdefault(v,[])
    def start(i): return ('s',i)
    def end(i): return ('t',i)
    chains = []
    for i in range(k):
        L = []
        def point(arr):
            v = (i,len(L)); L.append(v); z[v] = arr[:]; r[v] = 3*len(L)
        coords = [0]*k
        if i in I:
            for j in J: coords[j]=1
            point(coords)
            for j in J:
                coords[i]+=2; coords[j]=-1; point(coords)
                coords[i]+=2; coords[j]=1; point(coords)
        else:
            point(coords); point(coords)
        chains.append(L)
    def q(i,v): return r[v]+z[v][i]
    T = 10+max(q(i,v) for v in z for i in range(k))
    W = []
    for i,L in enumerate(chains):
        W.append([start(i)]+L+[end(i)])
        for h,L1 in enumerate(chains):
            for v in (L1 if h!=i else L1[:1]):
                edge(start(i),v,1+q(i,v))
        for u,v in zip(L,L[1:]): edge(u,v,q(i,v)-q(i,u))
        edge(L[-1],end(i),T-1-q(i,L[-1]))
    inf = sum(w for L in graph.values() for _,w in L)+1
    D = []
    for i in range(k):
        dist = {v:inf for v in graph}; ways = {v:0 for v in graph}
        dist[start(i)] = 0; ways[start(i)] = 1
        heap=[(0,0,start(i))]; stamp=0
        while heap:
            d,_,u=heapq.heappop(heap)
            if d!=dist[u]: continue
            for v,w in graph[u]:
                f=d+w
                if f<dist[v]:
                    stamp+=1; heapq.heappush(heap,(f,stamp,v)); dist[v]=f; ways[v]=ways[u]
                elif f==dist[v]: ways[v]+=ways[u]
        assert dist[end(i)]==T and ways[end(i)]==1
        assert all(dist[v]==1+q(i,v)<T for v in z)
        D.append({v:min(T,val) for v,val in dist.items()})
    P={v:[D[i][v]-D[-1][v] for i in range(k-1)] for v in graph}
    assert all(P[v]==z[v][:-1] for v in z)
    A=[(u,v) for L in W for u,v in zip(L,L[1:])]
    c=Q(1,2); M=T+1
    lo=[-M]*(k-1)
    for j in J:
        assert M-lo[j]==max(M-b for b in lo)
        assert lo[j]+Q(M-lo[j],3)<c<M-Q(M-lo[j],3)
        assert all(p[j]!=c for p in P.values())
        hits=0
        for u,v in A:
            x,y=P[u],P[v]
            if (x[j]<c)==(y[j]<c): continue
            t=(c-x[j])/(y[j]-x[j])
            if all(lo[h] <= (1-t)*x[h]+t*y[h] <=M for h in range(k-1)):
                hits+=1
        assert 2*len(I)<=hits<=2*len(I)+2*k<9*k
        lo[j]=c
    def inside(v): return all(lo[h]<=p<=M for h,p in enumerate(P[v]))
    count=sum(inside(u)!=inside(v) for u,v in A)
    assert count>=2*a*len(I)
    return len(graph),count
if __name__=='__main__':
    for k in range(4,31):
        n,b=check(k)
        print(f'{k=:2} {n=:4} {b=:4}')
