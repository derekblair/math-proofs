"""Local synthetic catalog counts. No real storage, credentials, or KEM calls."""
from itertools import combinations
from random import Random

def choices(groups, caps, k):
    def rec(j,remaining):
        if j==len(groups):
            yield ()
            return
        for m in range(min(remaining,caps[j],len(groups[j]))+1):
            for here in combinations(groups[j],m):
                for later in rec(j+1,remaining-m):
                    yield here+later
    return rec(0,k)

def coverage(groups,caps,k):
    return max(len(frozenset().union(*S)) for S in choices(groups,caps,k))

def singleton_matching(groups,caps,k):
    slots=[set().union(*g) for g,b in zip(groups,caps) for _ in range(b)]
    matched={}
    def aug(i, seen):
        for x in slots[i]-seen:
            seen.add(x)
            if x not in matched or aug(matched[x],seen):
                matched[x]=i
                return True
        return False
    n=sum(aug(i,set()) for i in range(len(slots)))
    return min(k,n)

def rainbow_exists(groups,k):
    flat=[(g,b) for g,S in enumerate(groups) for b in S]
    return any(len({g for g,_ in S})==k
               and len(frozenset().union(*(b for _,b in S)))==2*k
               for S in combinations(flat,k))

def colored_decision(groups,caps,k,labels,target_colors):
    p=max(labels.values(),default=-1)+1
    best={0:0}
    for group,b in zip(groups,caps):
        cur={0:0}
        for buf in group:
            m=sum(1<<x for x in set(map(labels.__getitem__,buf)))
            nxt=dict(cur)
            for u,w in cur.items():
                if w<b:
                    nxt[u|m]=min(nxt.get(u|m,k+1),w+1)
            cur=nxt
        nxt={}
        for u,w in best.items():
            for v,x in cur.items():
                if w+x<=k:
                    nxt[u|v]=min(nxt.get(u|v,k+1),w+x)
        best=nxt
    return target_colors in best

def main():
    r=Random(1813)
    for _ in range(1600):
        groups=[list({frozenset({r.randrange(7)}) for _ in range(r.randrange(6))})
                for _ in range(r.randrange(1,6))]
        caps=[r.randrange(3) for _ in groups]
        k=r.randrange(5)
        best=coverage(groups,caps,k)
        assert best==singleton_matching(groups,caps,k)
        # Identity coloring certifies the DP state exactly for every target mask.
        assert max(m.bit_count() for m in range(1<<7)
                   if colored_decision(groups,caps,k,dict(enumerate(range(7))),m))==best
    for _ in range(1200):
        dim=r.randrange(2,5)
        groups=[[] for _ in range(dim)]
        for u in range(dim):
            for v in range(dim):
                if r.random()<.42:
                    groups[(u+v)%dim].append(frozenset({u,v+dim}))
        assert all(len(set().union(*S))==2*len(S) for S in groups)
        k=r.randint(1,dim)
        assert (coverage(groups,[1]*dim,k)==2*k)==rainbow_exists(groups,k)
    print('1600 singleton-flow and exact mask-DP comparisons; 1200 disjoint-pair rainbow comparisons.')
if __name__=='__main__': main()
