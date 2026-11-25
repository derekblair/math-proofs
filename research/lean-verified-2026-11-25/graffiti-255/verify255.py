from itertools import combinations
q=4
m=q
V=set(range(2*m+3))
L=range(3,3+m)
R=range(3+m,3+2*m)
E={(0,1),(1,2)} | {(0,v) for v in L} | {(2,v) for v in R}
E |= {(u,v) for u,v in combinations(L,2) if (u-3)//q==(v-3)//q}
E |= {(u,v) for u in L for v in R if (u-3)%q==(v-(3+m))%q}
N={v:{b if a==v else a for a,b in E if v in (a,b)} for v in V}
def dist_row(v):
    layers=[{v},N[v],set().union(*(N[u] for u in N[v]))]
    assert set().union(*layers)==V
    return 1 if len(N[v])==len(V)-1 else 2
ecc={v:dist_row(v) for v in V}
C={v for v in V if ecc[v]==min(ecc.values())}
M=max(len(N[u]|N[v]) for u,v in E)
D={0,1,2}
assert all(a<b for a,b in E) and set().union(*(N[v] for v in D))==V
assert len(D)*M < 2*len(C)
print(dict(vertices=len(V),edges=len(E),center=len(C),eccentricity=set(ecc.values()),max_edge_neighborhood=M,lhs=len(D)*M,rhs=2*len(C)))
