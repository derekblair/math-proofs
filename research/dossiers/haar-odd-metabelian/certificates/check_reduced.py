"""Standalone exact arithmetic checker for finite rooted Haar base patches."""
import json
from pathlib import Path
from collections import defaultdict,Counter

def graph(kind, n, labels):
    if kind in {'cylinder','torus'}:
        def delta(j): return labels[j]
        N=3*n
        def adj(u,j):
            lower=u<N
            x,y=divmod(u%N,3)
            d,e=delta(j); x+=d if lower else -d; y+=e if lower else -e
            if kind=='torus':x%=n
            return 3*x+y%3+(N if lower else 0) if 0<=x<n else None
    else:
        N=n
        def adj(u,j):
            lower=u<N
            v=u%N+(labels[j] if lower else -labels[j])
            if kind=='cyclic': v%=N
            return v+(N if lower else 0) if 0<=v<N else None
    return N,adj

def check(path, kind, n, labels, start, equivariant=False):
    N,adj=graph(kind,n,labels)
    edges=sorted((u,v) for u in range(N) for j in range(3) if (v:=adj(u,j)) is not None)
    groups=[{u} for u in range(2*N)]
    complement=[]
    tree=defaultdict(set)
    for u,v in edges:
        a=next(g for g in groups if u in g)
        b=next(g for g in groups if v in g)
        if a is b: complement.append((u,v))
        else:
            groups.remove(b);a.update(b)
            tree[u].add(v);tree[v].add(u)
    assert len(groups)==1 and len(set(edges))==len(edges)
    dim=len(complement)
    def flow_for(data):
        chain=Counter()
        for coefficient,(u,v) in zip(data,complement):
            if not coefficient:continue
            prev={v:None}; queue=[v]
            for w in queue:
                for z in tree[w]:
                    if z not in prev:prev[z]=w;queue.append(z)
            assert u in prev
            seq=[u]
            while seq[-1]!=v:seq.append(prev[seq[-1]])
            ring=[u,*seq[::-1]]
            for w,z in zip(ring,ring[1:]):
                chain[(min(w,z),max(w,z))]+=coefficient*(1 if w<N else -1)
        chain={e:c for e,c in chain.items() if c}
        boundary=Counter()
        for (u,v),c in chain.items():
            boundary[u]-=c;boundary[v]+=c
        assert not any(boundary.values())
        assert tuple(chain.get(e,0) for e in complement)==tuple(data)
        return chain
    def orbits(data):
        result=[tuple(data)]
        chain=flow_for(data)
        if not chain:return result
        edge_set=set(edges)
        def add(translation):
            moved={tuple(map(translation,e)):c for e,c in chain.items()}
            assert moved.keys()<=edge_set
            result.append(tuple(moved.get(e,0) for e in complement))
        if kind=='cyclic':
            for shift in range(n):
                add(lambda u:(u%n+shift)%n+(n if u>=n else 0))
        elif kind=='cylinder':
            layer=lambda u:(u%N)//3
            pos=[layer(u) for e in chain for u in e]
            for shift in range(-min(pos),n-max(pos)):
                for twist in range(3):
                    add(lambda u:(layer(u)+shift)*3+(u%3+twist)%3+(N if u>=N else 0))
        else:raise ValueError('Unsupported equivariance')
        return list(dict.fromkeys(result))
    def expr(out, gens, proof):
        k,cs=proof
        assert type(k) is int and k>0 and k&(k-1)==0 and len(cs)==len(gens)
        assert all(type(c) is int for c in cs)
        assert all(sum(c*g[i] for c,g in zip(cs,gens))==k*out[i] for i in range(dim))
    def canon(v): return min(v,tuple(-z for z in v))
    def get(word):
        u=start;a=(0,)*dim;rows=[]
        assert len(word) in {4,8,16,32,64} and all(j in '012' for j in word)
        for j in map(int,word):
            v=adj(u,j)
            assert v is not None
            e=(min(u,v),max(u,v))
            rows.append((u,a))
            a=tuple(x+(1 if u<N else -1) if f==e else x for x,f in zip(a,complement))
            u=v
        assert u==start
        return canon(a), rows
    nodes=json.loads(Path(path).read_text())
    assert nodes[-1][0]==[]
    made={len(nodes)-1}
    for i in range(len(nodes)-1,-1,-1):
        assert i in made
        rels,path,close,branches=nodes[i]
        assert all(len(r)==dim and all(type(x) is int for x in r) for r in rels)
        w,rows=get(path);expr(w,rels,close)
        pairs=set()
        for j,(u,a) in enumerate(rows):
            for v,b in rows[:j]:
                if v==u:
                    d=canon(tuple(x-y for x,y in zip(a,b)))
                    assert any(d)
                    pairs.add(d)
        assert pairs=={tuple(d) for d,_,_ in branches} and len(pairs)==len(branches)
        for d,k,proofs in branches:
            assert type(k) is int and 0<=k<i
            made.add(k)
            new=nodes[k][0];assert len(new)==len(proofs)
            for v,proof in zip(new,proofs):
                expr(v,rels+(orbits(d) if equivariant else [d]),proof)
    return len(nodes),sum(len(row[3]) for row in nodes)

if __name__=='__main__':
    for kind,n,labels,start,sub,file in [
        ('strip',10,(0,1,3),4,'10-013','reduction_certificate.json'),
        ('strip',12,(0,1,4),5,'12-014','reduction_certificate.json'),
        ('strip',13,(0,2,5),5,'13-025','reduction_certificate.json'),
        ('torus',3,((0,0),(0,1),(1,0)),0,'torus-3','torus_certificate.json'),
        *[('cyclic',n,(0,1,3),0,f'closed-{n}-013','cyclic_certificate.json') for n in (7,9,11)],
        *[('cylinder',n,l,3*(n//2-1),f'cylinder-{n}-{i}','cylinder_certificate.json')
            for n in (4,5,6) for i,l in enumerate([((0,0),(0,1),(1,0)),((0,0),(1,0),(2,1))])],
    ]:
        fp=Path(__file__).with_name(sub)/file
        if fp.exists():print(sub,check(fp,kind,n,labels,start))
        e=fp.with_name('orbit_certificate.json')
        if e.exists():print(sub,'equivariant',check(e,kind,n,labels,start,True))
