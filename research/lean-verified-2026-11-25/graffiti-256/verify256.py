from itertools import combinations
V=set(range(15))
E={(0,1),(1,2)} | {(0,v) for v in range(3,9)} | {(2,v) for v in range(9,15)} | {(i,i+1) for i in (3,5,7,9,11,13)}
N={v:{b if a==v else a for a,b in E if v in (a,b)} for v in V}
union=lambda s:set().union(*(N[v] for v in s))
def connected():
    reached={0}
    for _ in V:
       reached |= union(reached)
    return reached==V
A={v for v in V if len(N[v])==min(map(len,N.values()))}
M=max(len(N[u]|N[v]) for u,v in E)
D={0,1,2}
assert all(a<b for a,b in E) and connected() and union(D)==V
assert all(union(s)!=V for s in combinations(V,2))
assert len(D)*M < 2*len(union(A))
print(dict(vertices=len(V),edges=sorted(E),degrees=[len(N[v]) for v in sorted(V)],A=sorted(A),N_A=sorted(union(A)),gamma=3,max_edge_neighborhood=M,lhs=len(D)*M,rhs=2*len(union(A))))
