from itertools import combinations, product
from math import comb

def sets(n,k): return map(frozenset, combinations(range(n), k))
def covers(blocks,n,c):
    return all(any(block.isdisjoint(s) for block in blocks) for s in sets(n,c))
def test_cover():
    total=0
    for n in range(1,10):
        for k in range(1,n+1):
            c=n-k
            blocks=list(sets(n,k))
            assert covers(blocks,n,c)
            for ix in range(len(blocks)):
                assert not covers(blocks[:ix]+blocks[ix+1:],n,c)
                total+=1
    for sizes in ([4,3],[3,3,3],[4,3,4],[4,5],[4],[2,4,3,3],[1,1,1]):
        n=sum(sizes)
        for k in range(1,min(sizes)+1):
            clusters=[]; off=0
            for s in sizes:
                clusters += [frozenset(i+off for i in members) for members in sets(s,k)]
                off+=s
            t=n-len(sizes)*(k-1)
            assert covers(clusters,n,t-1)
            assert not covers(clusters,n,t)
            assert len(clusters)==sum(comb(s,k) for s in sizes)
            total+=2
    return total

def test_witness_coupling():
    # n=4, c=f=1; two families of two disjoint blocks. Integer message operation XOR.
    # Observer picks endpoint from challenge material, then a family and acceptance
    # using the actual values exposed in the first and second steps.
    from collections import Counter
    W=[(i,j) for i in range(2) for j in range(2)]
    for candidate in W:
        hist=[Counter(),Counter()]
        cand_ix=W.index(candidate)
        for secret in range(2):
            for a,b,d in product(range(2),repeat=3):
                vals=a,b,d,a^b^d^secret
                for masks in product(range(2),repeat=8):
                    ct=tuple(vals[h//2]^masks[h] for h in range(8))
                    e=ct[0]+2*ct[4]
                    if e//2==candidate[1]:
                        continue
                    e_reads=tuple(masks[4*i+e] for i in range(2))
                    i=ct[7]^e_reads[0]^e_reads[1]
                    if i==candidate[0]:
                        continue
                    i_reads=masks[4*i:4*i+4]
                    first=next(w for w in W if w[0]!=i and w[1]!=e//2)
                    if first!=candidate: continue
                    assert all(4*i+off not in (2*cand_ix,2*cand_ix+1) for off in range(4))
                    hist[secret][(ct,e,e_reads,i,i_reads)] += 1
        assert hist[0]==hist[1] and hist[0]
    return len(W)*2*8*256

if __name__=="__main__":
    print(f"{test_cover()} covering checks, {test_witness_coupling()} exact joint transcript controls")
