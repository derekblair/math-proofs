"""Independent exact checker of the finite clique-elimination certificate."""
import json
from collections import defaultdict
from itertools import combinations
from pathlib import Path

n, m = 15, 4092
U = (1 << n) - 1
data = json.loads(Path("proof-data15.json").read_text())
paint = {int(a): c for a, c in data["p"].items()}
rows = data["r"]

def intersection_min(a, b):
    """Deadline-greedy minimum intersection; do not use prefix maximum."""
    available, hits = U, 0
    while b:
        first = b & -b
        poss = available & ((first << 1) - 1)
        free = poss & ~a
        if free:
            available ^= free & -free
        else:
            assert poss
            available ^= poss & -poss
            hits += 1
        b ^= first
    return hits

def adjacent(a, b):
    return intersection_min(a,b) >= max(2, a.bit_count()+b.bit_count()-13)

def profile(a):
    return tuple((a & ((1 << t) - 1)).bit_count() for t in range(n+1))

def anchor(a):
    return (a & 63).bit_count() >= 4 and (a >> 7).bit_count() <= 3

assert set(paint) == {a for a in range(1 << n) if adjacent(a,a)}
C = {a for a in paint if anchor(a)}
assert len(C) == m
classes = defaultdict(list)
for a,c in paint.items():
    classes[c].append(a)
K = len(classes)
assert K == 4106 and set(classes) == set(range(K))
assert all(not adjacent(a,b) for c in classes.values() for a,b in combinations(c,2))
P = {a:profile(a) for a in paint}
bank = defaultdict(list)
by_label = {}
for s, k, a, miss in rows:
    assert s in (0,1) and a in paint and not anchor(a) and k == a.bit_count()
    assert a not in by_label
    by_label[a] = (s, k, miss)
    bank[s,k].append(a)

def dominate(a,b):
    return all(x>=y for x,y in zip(P[a],P[b]))

def coarse(a):
    k = a.bit_count()
    if any(dominate(b,a) for b in bank[0,k]):
        return 0
    return 2 if anchor(a) else 1

stages = {a:coarse(a) for a in paint}
num_edges = 0
for s,k,a,miss in rows:
    assert stages[a] == s
    assert len(miss)==len(set(miss))==15 and all(c in classes for c in miss)
    for c in miss:
        for b in classes[c]:
            if a!=b and stages[b]>=s:
                assert not adjacent(a,b), (a,b)
                num_edges+=1
for a,s in stages.items():
    if s<2:
        assert any(dominate(b,a) for b in bank[s,a.bit_count()])
assert len(rows)==36
assert {a for a,s in stages.items() if s==2}==C
print(f"Independent exact check: {len(paint)} admissibles, {K} proper colors, "
      f"{len(rows)} pivot rows, {num_edges} omissions, cap {m}.")
