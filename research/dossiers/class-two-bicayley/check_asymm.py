#!/usr/bin/env python3
"""Independent finite check of the class-two 270-vertex control."""
from itertools import product

Q = tuple(product(range(3), range(3), range(3), range(5)))
V = tuple(product(range(2), Q))
identity = (0, 0, 0, 0)
a, ai = (1, 0, 0, 0), (2, 0, 0, 0)
b, bi = (0, 1, 0, 1), (0, 2, 0, 4)

def mul(u, v):
    x, y, z, t = u
    X, Y, Z, T = v
    return ((x+X) % 3, (y+Y) % 3, (z+Z+x*Y) % 3, (t+T) % 5)

adj = {}
for i, u in V:
    r, ri = (a, ai) if i == 0 else (b, bi)
    adj[i, u] = {(1-i, u), (i, mul(u, r)), (i, mul(u, ri))}
assert len(adj) == 270
assert all(len(ns) == 3 and v not in ns and all(v in adj[w] for w in ns)
           for v, ns in adj.items())

def walkset(root):
    reached = {root}
    todo = [root]
    while todo:
        for v in adj[todo.pop()] - reached:
            reached.add(v)
            todo.append(v)
    return reached

assert len(walkset((0, identity))) == 270

def rooted_cycle(origin, n):
    def extend(path):
        end = path[-1]
        if len(path) == n:
            return path if origin in adj[end] else None
        for v in sorted(adj[end] - set(path)):
            candidate = extend(path + (v,))
            if candidate:
                return candidate
        return None
    return extend((origin,))

assert rooted_cycle((0, identity), 3)
assert not rooted_cycle((1, identity), 3)
assert all(rooted_cycle(v, n) is None for v in V for n in (4, 8))
assert rooted_cycle((0, identity), 16)
print("270 vertices; simple, cubic, connected; not vertex-transitive; C16 but no C4 or C8.")
