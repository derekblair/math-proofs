"""Independent standard-library certificate checker, using integer lifts, no search."""
import json
from pathlib import Path

ZERO=(0,0,0,0)
COTREE=((1,4),(1,5),(2,4),(2,5))
def verify_expr(out, gens, proof):
    k, cs=proof
    assert type(k) is int and k>0 and k&(k-1)==0 and len(cs)==len(gens)
    assert type(cs) is list and all(type(c) is int for c in cs)
    assert all(sum(c*g[i] for c,g in zip(cs,gens))==k*out[i] for i in range(4))
def trace(word):
    u=0; a=ZERO; rows=[]
    assert len(word) in {4,8,16,32} and all(j in '012' for j in word)
    for j in map(int,word):
        rows.append((u,a))
        v=3+(u+j)%3 if u<3 else (u-3-j)%3
        edge=(min(u,v),max(u,v))
        a=tuple(z+((1 if u<3 else -1) if e==edge else 0) for z,e in zip(a,COTREE))
        u=v
    assert u==0
    return a, rows
def check(nodes):
    assert nodes[-1][0]==[]
    reachable={len(nodes)-1}
    for i in range(len(nodes)-1,-1,-1):
        assert i in reachable
        rels, w, closure, branches=nodes[i]
        assert all(len(r)==4 and all(type(c) is int for c in r) for r in rels)
        close,rows=trace(w)
        verify_expr(min(close,tuple(-c for c in close)),rels,closure)
        fail=set()
        for j,(u,a) in enumerate(rows):
            for v,b in rows[:j]:
                if u==v:
                    d=tuple(x-y for x,y in zip(a,b))
                    assert d!=ZERO
                    fail.add(min(d,tuple(-c for c in d)))
        assert fail=={tuple(d) for d,_,_ in branches} and len(fail)==len(branches)
        for d,child,proves in branches:
            assert type(child) is int and 0<=child<i
            reachable.add(child)
            new=nodes[child][0]
            assert len(proves)==len(new)
            for r,proof in zip(new,proves):
                verify_expr(r,rels+[d],proof)
    return len(nodes)

if __name__=='__main__':
    nodes=json.loads(Path(__file__).with_name('cover_certificate.json').read_text())
    print(f'{check(nodes)} validated induction states')
