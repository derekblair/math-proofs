from itertools import combinations
from collections import defaultdict
from random import Random
from math import comb
r=Random(5633221)
def close(n,pct):
    d=[sum((1<<i) for i in range(j) if r.randrange(100)<pct) for j in range(n)]
    for j in range(n):
        for i in range(j-1,-1,-1):
            if d[j]>>i&1:d[j]|=d[i]
    return d
def ext(d):
    n=len(d)
    def go(mask,w):
        if len(w)==n:
            yield w
            return
        for i in range(n):
            if not(mask>>i&1) and d[i]&mask==d[i]:
                yield from go(mask|1<<i,(*w,i))
    return list(go(0,()))
def paths(m,b):
    out=[]
    for ii in combinations(range(1,m+1),b):
        w=0; J=[]
        for k in range(m+1):
            w+=int(k in ii);J.append(w)
        out.append(tuple(J))
    return out
pathcache={(m,b):paths(m,b) for m in range(2,9) for b in range(1,m)}
sizes=[0]*6
for n in range(3,9):
  for seed in range(38):
    d=close(n,(23,37,61,74)[seed%4]); es=ext(d)
    up=[sum(1<<j for j in range(n) if d[j]>>i&1) for i in range(n)]
    for x in range(n):
      for y in range(n):
        if x==y or (d[x]>>y)&1 or (d[y]>>x)&1:continue
        aa=(up[x]&~up[y])|(1<<x)
        bb=(d[y]&~d[x])|(1<<y)
        assert not(aa&bb)
        m=(aa|bb).bit_count(); b=bb.bit_count()
        f=defaultdict(set)
        for e in es:
            A=tuple(i for i in e if aa>>i&1); B=tuple(i for i in e if bb>>i&1)
            O=tuple((k,i) for k,i in enumerate(e) if not((aa|bb)>>i&1))
            j=0; prefix=[0]
            for i in e:
                if (aa|bb)>>i&1:
                    j+=int(bb>>i&1);prefix.append(j)
            f[(A,B,O)].add(tuple(prefix))
        reverse=tuple(min(k,b) for k in range(m+1))
        assert len(f)*comb(m,b)>=len(es)
        sizes[0]+=1;sizes[1]+=len(f)
        for got in f.values():
            assert reverse in got
            low=tuple(map(min,zip(*got)))
            assert low in got
            assert got=={p for p in pathcache[m,b] if all(x>=y for x,y in zip(p,low))}
            sizes[2]+=len(got);sizes[3]+=int(len(got)>1);sizes[4]+=int(1<len(got)<comb(m,b));sizes[5]+=int(len(got)==comb(m,b))
print('pairs,fibers,extensions,nonsingleton,proper nonsingleton,full',*sizes)
