"""Exact graph witness in the double lamp F3^14 semidirect C7 model."""
N=7
def addvec(u,i,z):
    v=list(u);v[i]=(v[i]+z)%3
    return tuple(v)
def edge(g,c):
    d,s,u=g
    t=(s+c if d==0 else s-c)%N
    return (1-d,t,u if c==0 else addvec(u,7*(c-1)+(s if d==0 else t),1 if d==0 else -1))
root=(0,0,(0,)*14)
rings={}
paths={}
def dfs(g,vs,ps):
    if len(ps)==16:
        for w,labels in paths.get(g,()):
            if not set(w[1:-1]).intersection(vs[1:-1]):
                word=ps+labels[::-1]
                assert verify(word)
                return word
        paths.setdefault(g,[]).append((vs,ps))
        return
    for c in range(3):
        t=edge(g,c)
        if t not in vs:
            ans=dfs(t,vs+(t,),ps+(c,))
            if ans:return ans
def verify(word):
    g=root; v={g}
    for i,p in enumerate(word):
        g=edge(g,p)
        if i+1==len(word):return g==root and len(v)==len(word)
        assert g not in v;v.add(g)
r=dfs(root,(root,),())
assert r and len(r)==32
print('32-cycle at identity:', ''.join(map(str,r)))
def check_small_brutal():
    n={4:0,8:0,16:0}; samples={}
    def rec(g,vs,ps):
        if len(ps)==16:return
        for c in range(3):
            t=edge(g,c)
            m=len(ps)+1
            if t==root and m in n:
                n[m]+=1;samples.setdefault(m,ps+(c,))
            elif t not in vs:rec(t,vs+(t,),ps+(c,))
    rec(root,(root,),())
    print('simple cycles from identity:',n,samples)
check_small_brutal()
