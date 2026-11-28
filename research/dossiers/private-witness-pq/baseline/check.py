"""Replay only the documented public-catalogue comparison, not a proof of optimality."""
from itertools import combinations
from math import comb
from pathlib import Path
here=Path(__file__).resolve().parent
rows=[(20,10,812,1,'w-20-9-1.txt'),(19,9,489,2,'w-19-8-2.txt'),(18,9,722,4,'w-18-8-1.txt')]
for n,h,w,g,name in rows:
    support=list(map(int,(here/name).read_text().split()))
    assert len(support)==len(set(support))==w
    assert all(0<x<1<<n and x.bit_count()==7 for x in support)
    covered=set()
    for x in support:
        complement=[i for i in range(n) if (x>>i)&1==0]
        covered.update(sum(1<<i for i in row) for row in combinations(complement,h-1))
    assert len(covered)==comb(n,h-1)
    print(n,h,w,len(covered))
assert sum(n*g for n,h,w,g,name in rows)==130
assert sum(h*g for n,h,w,g,name in rows)==64
assert sum((n-6)*g for n,h,w,g,name in rows)==88
assert sum(w*g for n,h,w,g,name in rows)==4678
print('130 sites; 64 credits; 88 selected; 4678 public supports')
