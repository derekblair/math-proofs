from collections import defaultdict
from itertools import product
from random import Random
from two_anchor import adj, search, strong, minimal

def reach(n,E):
    A=adj(n,E)
    return [set(search(A,i)) for i in range(n)]

def trim_one(n,E):
    E=set(E); indeg=[0]*n; outdeg=[0]*n
    for u,v in E: indeg[v]+=1;outdeg[u]+=1
    for u,v in sorted(E):
        if indeg[v]>1 and outdeg[u]>1:
            E.remove((u,v));indeg[v]-=1;outdeg[u]-=1
    return E

def lift(n,E,F):
    Rt=reach(n,E); lab={}; lists=[]
    for u in range(n):
        if u not in lab:
            C=sorted(v for v in Rt[u] if u in Rt[v])
            for v in C: lab[v]=len(lists)
            lists.append(C)
    cn=len(lists)
    gs={lab[f] for f in F}
    groups=defaultdict(list); interior=defaultdict(set)
    for x,y in sorted(E):
        if lab[x]==lab[y]: interior[lab[x]].add((x,y))
        else: groups[lab[x],lab[y]].append((x,y))
    H=adj(cn,groups); Hr=adj(cn,groups,1)
    seeds=[]
    for f in gs:
        D=set(search(H,f)); A=set(search(Hr,f))
        In={y for x,y in groups if x!=f and x in D}
        Out={x for x,y in groups if y!=f and y in A}
        seeds.append((f,D,A,In,Out))
    ED={e for e in E if F.isdisjoint(e)}
    # Oracle for the cited dynamic DAG reduction, deliberately recomputed
    # for independent correctness tests only.
    DagTR={e for e in ED if e[1] not in search(adj(n,ED-{e}),e[0])}
    out=set()
    for X,Y in groups:
        x,y=groups[X,Y][0]
        via=any((Y in In if X==f else X in Out if Y==f else X in A and Y in D)
                for f,D,A,In,Out in seeds)
        if not via and (X in gs or Y in gs or (x,y) in DagTR):out.add((x,y))
    for i,C in enumerate(lists):
        if len(C)==1:continue
        cF=sorted(set(C)&F)
        assert 1<=len(cF)<=2
        P=cF+[v for v in C if v not in F]
        idx={v:p for p,v in enumerate(P)}
        E2={(idx[x],idx[y]) for x,y in interior[i]}
        H2=trim_one(len(P),E2) if len(cF)==1 else minimal(len(P),E2)
        out.update((P[x],P[y]) for x,y in H2)
    return out

def run():
    rng=Random(776312); checked=0
    edgechanges=[0,0]
    for n in range(3,19):
      for k in (1,2):
        F=set(range(k))
        edges=[(u,v) for u in range(n) for v in range(n)
               if u!=v and (u in F or v in F or u<v)]
        for _ in range(5):
          E=set()
          for t in range(110):
            if t%2==0 or not E:
                z=rng.randrange(n)
                d={e for e in edges if z in e and e not in E and rng.random()<.27}
                E|=d;edgechanges[0]+=len(d)
            else:
                d={e for e in E if rng.random()<.18}
                E-=d;edgechanges[1]+=len(d)
            O=lift(n,E,F); D=reach(n,E)
            assert O<=E and reach(n,O)==D
            for x,y in O:
                assert y not in search(adj(n,O-{(x,y)}),x)
            checked+=1
    print(checked,'intermediate fully dynamic reductions;',edgechanges,'inserted/deleted arcs')
if __name__=='__main__':run()
