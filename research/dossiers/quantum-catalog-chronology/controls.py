"""Synthetic checks of query-slot combinatorics and weighted matching gadget."""
from functools import lru_cache
from itertools import combinations, product
from random import Random

def subset(T,k):
    T=tuple(T)
    return [frozenset(s) for j in range(min(k,len(T))+1) for s in combinations(T,j)]

def rounded(groups, caps, Q):
    return max(len(frozenset().union(*S)) for S in product(*(subset(g,2*q) for g,q in zip(groups,caps)))
               if sum((len(s)+1)//2 for s in S)<=Q)

def path_pairs(groups,caps,Q):
    best=0
    for slots in product(*(range(q+1) for q in caps)):
        if sum(slots)>Q: continue
        paths=[frozenset().union(*S) for S in product(*(subset(g,L) for g,L in zip(groups,slots)))]
        best=max(best,max(len(a|b) for a in paths for b in paths))
    return best

def weighted_gadget(groups,caps,Q,n):
    S=sum(caps)
    Q=min(Q,S)
    M=n+1
    V=n+4*S
    adj=[{} for _ in range(V)]
    def edge(a,b,w): adj[a][b]=adj[b][a]=w
    i=0
    for phase,t in enumerate(caps):
        for j in range(t):
            u=n+4*i; v=u+1
            edge(u,v,2*M)
            edge(u,u+2,M); edge(v,u+3,M)
            for label in groups[phase]:
                edge(u,label,M+1)
                edge(v,label,M+1)
            i+=1
    @lru_cache(None)
    def dp(mask,k):
        if k==0:return 0
        if mask.bit_count()<2*k:return -10**9
        u=(mask&-mask).bit_length()-1
        rest=mask^(1<<u)
        val=dp(rest,k)
        for v,w in adj[u].items():
            if rest>>v&1:
                val=max(val,w+dp(rest^(1<<v),k-1))
        return val
    ans=dp((1<<V)-1,S+Q)
    return ans-2*S*M

def paired_reduction(T,k):
    groups=[]
    for i,(x,y,z) in enumerate(T):
        groups.append(({('X',x),('Y',y)},{('Z',z),('D',i)}))
    mx=0
    for selected in subset(range(len(T)),k):
        mx=max(mx,len(set().union(*(g for i in selected for g in groups[i]))))
    ok=any(len({x for x,y,z in A})==len({y for x,y,z in A})==len({z for x,y,z in A})==k
           for A in combinations(T,k))
    assert (mx>=4*k)==ok

def main():
    r=Random(1902)
    for _ in range(550):
        E=r.randrange(1,4); n=r.randrange(1,7)
        groups=[{i for i in range(n) if r.random()<.5} for _ in range(E)]
        caps=[r.randrange(2) for _ in range(E)]
        Q=r.randrange(4)
        expected=rounded(groups,caps,Q)
        assert expected==path_pairs(groups,caps,Q)==weighted_gadget(groups,caps,Q,n)
    assert rounded([{0},{1}],[1,1],1)==1
    T=list(product(range(3),repeat=3))
    for _ in range(900):
        sample=r.sample(T,r.randrange(0,8))
        paired_reduction(sample,r.randrange(1,4))
    print('550 rounded budgets, coherent path-pair maxima and optimal weighted matching gadget checks.')
    print('900 exact small disjoint-pair catalog / three-dimensional matching equivalence checks.')
if __name__=='__main__': main()
