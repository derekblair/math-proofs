#!/usr/bin/env python3
"""Independent exact arithmetic check; no Mathlib or generated distance tables."""
from fractions import Fraction
from gen269 import generate

G = generate(35, 62)
n = len(G)
assert n == 268
assert all(u not in nei and all(u in G[v] for v in nei) for u, nei in enumerate(G))
assert max(len(G[u] & G[v]) for u in range(n) for v in range(u)) == 1
assert all(G[u] & {0, 1, 2, 3} for u in range(n))
D = [[0 if u == v else 1 if v in G[u] else n for v in range(n)] for u in range(n)]
for k, row in enumerate(D):
    for other in D:
        left = other[k]
        if left >= n:
            continue
        for v, right in enumerate(row):
            if left + right < other[v]:
                other[v] = left + right
assert all(max(row) == 4 for row in D)
assert sum(map(sum, D)) == 214680
avg = Fraction(sum(map(sum, D)), n * (n - 1))
assert avg == Fraction(17890, 5963) and 3 < avg < 4
print(n, "vertices;", sum(map(len, G)) // 2, "edges")
print(n, "centers; radius 4; C4-free; four explicitly listed total dominators")
print("ordered sum =", sum(map(sum,D)), "; pairs =", n*(n-1), "; average =", avg)
print("floor(1 + average) = 4; ceiling(1 + average) = 5")

# Negative controls distinguish the strict distance threshold and forbid all C4s.
near = generate(35, 61)
from gen269 import distances
near_D = distances(near)
near_n = len(near)
near_gap = sum(map(sum, near_D)) - 3*near_n*(near_n-1)
assert near_gap == -4
with_c4 = [set(row) for row in G]
with_c4[4].add(8)
with_c4[8].add(4)
assert {6, 8} <= with_c4[0] & with_c4[4]
print("Controls: one fewer plain track gives excess", near_gap,
      "; one added edge creates a four-cycle.")
