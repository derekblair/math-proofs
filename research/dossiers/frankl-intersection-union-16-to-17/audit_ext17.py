"""Independent exact deadline audit of the n17 auxiliary-palette proof."""
import json
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path

n, m = 17, 17298
U = (1 << n) - 1
data = json.loads(Path("proof-data17.json").read_text())
paint = {int(a):c for a,c in data["p"].items()}
rows=data["r"]

def minimum(a,b):
    avail,hits=U,0
    while b:
        first=b&-b
        pos=avail&((first<<1)-1)
        free=pos&~a
        if free:
            avail^=free&-free
        else:
            assert pos
            avail^=pos&-pos
            hits+=1
        b^=first
    return hits

def edge(a,b):
    return minimum(a,b)>=max(2,a.bit_count()+b.bit_count()-15)

assert set(paint)=={x for x in range(1<<n) if edge(x,x)}
cls=defaultdict(list)
for a,c in paint.items():cls[c].append(a)
K=len(cls)
assert K==17467 and set(cls)==set(range(K))
assert all(not edge(a,b) for C in cls.values() for a,b in combinations(C,2))
anchor=lambda a:(a&255).bit_count()>=5 and (a>>9).bit_count()<=3
P={a:tuple((a&((1<<t)-1)).bit_count() for t in range(18)) for a in paint}
bank=defaultdict(list)
for s,k,a,miss in rows:
    assert s in (0,1,2) and k==a.bit_count() and a in P
    assert len(miss)==len(set(miss))==K-m+1
    assert all(c in cls for c in miss)
    bank[s,k].append(a)
def stage(a):
    for s in (0,1,2):
        if any(all(x>=y for x,y in zip(P[b],P[a])) for b in bank[s,a.bit_count()]):
            return s
    return 3
stamps={a:stage(a) for a in paint}
assert {a for a,t in stamps.items() if t==3}=={a for a in paint if anchor(a)}
assert Counter(stamps.values())=={0:21390,1:4854,2:14,3:17298}
x=0
for s,k,a,miss in rows:
    assert stamps[a]==s
    for c in miss:
        for b in cls[c]:
            if b!=a and stamps[b]>=s:
                assert not edge(a,b),(s,a,b)
                x+=1
print(f"Independent exact check: {len(paint)} admissibles, {K} auxiliary colors, "
      f"{len(rows)} pivot rows, {x} live omissions, cap {m}.")
