"""Search a finite certificate for all odd abelian quotients of the K3,3 cycle lattice."""
from functools import lru_cache
from itertools import islice
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
from k33_homology import zero, step, words
P=101 # integral coordinates represented by residues; all words have length <=32.
def diff(A,B):
    return tuple((a-b+50)%P-50 for a,b in zip(A,B))
def canon(d):
    return min(d,tuple(-v for v in d))
def certificate(W,close_universal_only=False):
    s=(0,zero); seen=[]; fail=set()
    for j in W:
        for v in seen:
            if v[0]!=s[0]:continue
            a=canon(diff(v[1],s[1]))
            if a==zero:return
            fail.add(a)
        seen.append(s);s=step(s,j,P)
    if s[0]==0 and (not close_universal_only or s[1]==zero):
        return (canon(diff(s[1],zero)),tuple(sorted(fail)),W)
def space(rels):
    return tuple(tuple(map(int,col)) for col in zip(*hermite_normal_form(Matrix(4,len(rels),lambda i,j:rels[j][i])).tolist()))
@lru_cache(maxsize=None)
def membership(H):
    if not H:return lambda r:r==zero
    mat=Matrix(4,len(H),lambda i,j:H[j][i])
    _,pivot=mat.T.rref()
    small=mat[list(pivot),:]
    T=small.inv()
    @lru_cache(maxsize=None)
    def contains(r):
        a=T*Matrix([r[i] for i in pivot])
        if any(int(z.q)&(int(z.q)-1) for z in a):return False
        return list(mat*a)==list(r)
    return contains
@lru_cache(maxsize=None)
def quotient_key(H):
    if not H:return lambda r:r
    mat=Matrix(4,len(H),lambda i,j:H[j][i])
    _,pivot=mat.T.rref()
    T=mat[list(pivot),:].inv()
    @lru_cache(maxsize=None)
    def calc(r):
        a=T*Matrix([r[i] for i in pivot])
        residual=tuple(Matrix(r)-mat*a)
        def oddpart(z):
            q=int(z.q); k=(q&-q)
            q//=k
            return (int(z.p)*pow(k,-1,q)%q,q) if q>1 else (0,1)
        return residual+tuple(map(oddpart,a))
    return calc
def find_at(H,n,half_words):
    value=quotient_key(H)
    iszero=membership(H)
    bins={}
    for w,s in half_words:
        key=(s[0],value(diff(s[1],zero)))
        for v in bins.setdefault(key,[]):
            if w[0]==v[0] or w[-1]==v[-1]:continue
            D=certificate(w+v[::-1])
            if D is not None and iszero(D[0]) and not any(iszero(d) for d in D[1]):return D
        bins[key].append(w)
def short(n):
    for w,s in words(n,0,P):
        if s[0]==0:
            D=certificate(w)
            if D is not None:yield D
def universal32(limit):
    d={}
    for w,s in words(16,0,P):
        for v in d.setdefault(s,[]):
            if w[0]==v[0] or w[-1]==v[-1]:continue
            D=certificate(w+v[::-1],True)
            if D is not None:yield D
        d[s].append(w)
        if len(d)>=limit:return
def witness(rels,r):
    from math import lcm
    from sympy import ZZ
    from sympy.polys.matrices.normalforms import smith_normal_decomp
    if not rels:
        assert r==zero
        return [1,[]]
    M=Matrix(4,len(rels),lambda i,j:rels[j][i])
    D,U,V=(x.to_Matrix() for x in smith_normal_decomp(M.to_DM(domain=ZZ)))
    rhs=U*Matrix(r)
    t=Matrix.zeros(len(rels),1)
    for i,u in enumerate(rhs):
        if i<min(D.shape) and D[i,i]:
            t[i,0]=u/D[i,i]
        else: assert u==0
    w=V*t
    k=lcm(*(int(z.q) for z in w))
    assert k > 0 and k&(k-1)==0
    assert M*w==Matrix(r)
    return [k,[int(k*z) for z in w]]

if __name__=='__main__':
    import json
    root=certificate(tuple(map(int,'10101010101012010102010121010120')))
    cs=list(short(4))+list(short(8))+[root]
    cs+=list(islice(universal32(100000),128))
    half={n:words(n//2,0,P) for n in (16,32)}
    nodes={}
    print('initial candidates',len(cs),flush=True)
    @lru_cache(maxsize=None)
    def visit(H):
        iszero=membership(H)
        C=[(len(ds),w,z,ds) for z,ds,w in cs if iszero(z) and not any(iszero(a) for a in ds)]
        if not C:
            for n in (16,32):
                D=find_at(H,n,half[n])
                if D is not None:
                    z,ds,w=D
                    C=[(len(ds),w,z,ds)]
                    break
            else:
                raise ValueError(f'stuck {H}')
        _,w,z,fails=min(C)
        branches=[]
        for a in fails:
            assert not iszero(a)
            B=space(H+(a,))
            child=visit(B)
            branches.append([a,child,[witness(H+(a,),b) for b in B]])
        i=len(nodes)
        nodes[i]=[H,''.join(map(str,w)),witness(H,z),branches]
        return i
    root=visit(())
    from collections import Counter
    print(root,len(nodes),Counter(len(n[1]) for n in nodes.values()),visit.cache_info())
    with open('cover_certificate.json','w') as f:
        json.dump(list(nodes.values()),f,separators=(',',':'))
        f.write('\n')
