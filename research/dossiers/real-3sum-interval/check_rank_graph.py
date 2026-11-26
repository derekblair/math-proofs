"""Independent exact implementation of the Lemma 5.8 incidence count on tiny tied inputs."""
from collections import defaultdict
from itertools import product
import random

def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def add(a,b): return (a[0]+b[0],a[1]+b[1])

def path_halves(r, side, size):
    level=1
    while level < size:
        if (r//level)%2==side:
            yield level,r//(2*level)
        level*=2

def rank_graph(aa,bb,I,degree,s):
    d=len(aa[0]); r=range(d)
    diffs=sorted({sub(row[i],row[j]) for rows in (aa,bb) for row in rows for i,j in product(r,repeat=2)})
    idx={x:i for i,x in enumerate(diffs)}
    size=1
    while size<=len(diffs): size*=2
    lead=[]
    for role,rows in enumerate((aa,bb)):
        table=defaultdict(list)
        for i,row in enumerate(rows):
            for p in r:
                for k,ell in product(I,r):
                    for ext in product(r,repeat=2*s):
                        sel=idx[sub(row[k],row[p])] if role==0 else idx[sub(row[p],row[ell])]
                        xs=[sel]
                        for t in range(s):
                            v,w=ext[2*t:2*t+2]
                            xs.append(idx[sub(row[v],row[k])] if role==0 else idx[sub(row[ell],row[w])]+1)
                        for witness in product(*(path_halves(x,role,size) for x in xs)):
                            table[k,ell,ext,witness].append((i,p))
        lead.append(table)
    light,heavy=defaultdict(int),defaultdict(int)
    for key,left in lead[0].items():
        right=lead[1].get(key,())
        buckets=heavy if len(left)+len(right)>degree else light
        for a,b in product(left,right): buckets[a,b]+=1
    return light,heavy

def test():
    rng=random.Random(4412)
    tests=0
    for d in (2,):
      for t in range(2):
        m=2
        aa=[sorted((rng.randint(-2,2),i*d+k+1) for k in range(d)) for i in range(m)]
        bb=[sorted((rng.randint(-2,2),(i*d+k+1)*(m*d+1)) for k in range(d)) for i in range(m)]
        intervals=[range(i,i+l) for l in [1,2,4] if l<=d for i in range(0,d,l)]
        for I,s in product(intervals,range(3)):
            light,heavy=rank_graph(aa,bb,I,2+t,s)
            for i,j,p,q in product(range(m),range(m),range(d),range(d)):
                sums={(k,l):add(aa[i][k],bb[j][l]) for k,l in product(range(d),repeat=2)}
                ranks={z:k+1 for k,z in enumerate(sorted(sums.values()))}
                expected=sum(ranks[sums[k,l]]**s for k,l in product(I,range(d)) if sums[k,l]<sums[p,q])
                assert light[(i,p),(j,q)]+heavy[(i,p),(j,q)]==expected
                tests+=1
    print('pointwise strict count controls:',tests)
if __name__=='__main__': test()
