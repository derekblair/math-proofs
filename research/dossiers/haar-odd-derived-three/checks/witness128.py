"""Exact compressed walk for the mod-3 cover of the m=13, p=5 lamp example."""
M,P=13,5
base=(0,0,(0,)*26)
A=tuple(map(int,'0120121010121021010101'))
def move(g,c):
    d,s,v=g
    delta=(0,1,4)[c]
    t=(s+delta if d==0 else s-delta)%M
    if c:
        u=(c-1)*M+(s if d==0 else t)
        v=v[:u]+((v[u]+(1 if d==0 else -1))%P,)+v[u+1:]
    return 1-d,t,v
def path(g,w):
    v=[g]
    for c in w:
        g=move(g,c);v.append(g)
    return tuple(v)
X=path(base,A);S=set(X[:-1])
assert len(A)==22 and len(S)==22 and X[-1]==base
def search(g,vertices,w):
    if len(w)==10:
        for i in range(0,22,2):
            B=A[i:]+A[:i]
            if w[-1] in (B[0],B[-1]):continue
            Y=path(g,B)
            if not set(Y[:-1]) & (S | set(vertices[:-1])):
                T=w+B+w[::-1]
                return w,B,A+T+A[::-1]+T[::-1]
        return
    for c in range(3):
        if (not w and c in (A[0],A[-1])) or (w and c==w[-1]):continue
        v=move(g,c)
        if v not in S and v not in vertices:
            ans=search(v,vertices+(v,),w+(c,))
            if ans:return ans
C,B,W=search(base,(base,),())
assert len(W)==128
def lift_check(w):
    v=base; lamps={}; seen=set()
    for c in w:
        full=(v,frozenset(lamps.items()))
        assert full not in seen
        seen.add(full)
        u=move(v,c)
        if c:
            k=c, v if v[0]==0 else u
            a=(lamps.get(k,0)+(1 if v[0]==0 else -1))%3
            if a:lamps[k]=a
            else:lamps.pop(k,None)
        v=u
    assert v==base and not lamps
lift_check(W)
print('C22:', ''.join(map(str,A)), ''.join(map(str,B)))
print('bridge', ''.join(map(str,C)))
print('simple C128 upstairs:', ''.join(map(str,W)))
