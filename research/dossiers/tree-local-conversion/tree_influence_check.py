"""Independent checks of literal local Algorithm 2 against bottom-up evaluation."""
from collections import deque
from random import Random


def distances(adj, allowed, root):
    d = {root: 0}
    todo = deque([root])
    while todo:
        u = todo.popleft()
        for v in adj[u]:
            if v in allowed and v not in d:
                d[v] = d[u] + 1
                todo.append(v)
    return d


def ref(adj, k, threshold, root, scope):
    committed, equal = set(), set()
    for u in scope:
        child = frozenset(v for v, d in distances(adj, scope, u).items() if d <= k)
        if child == scope:
            equal.add(u)
        elif ref(adj, k, threshold, u, child):
            committed.add(u)
    for i in range(len(committed) + len(equal), -1, -1):
        if len(committed) + sum(threshold[u] <= i for u in equal) >= i:
            return i >= threshold[root]
    raise AssertionError("zero is feasible")


def dp(adj, k, threshold, root_scope=None):
    allowed = frozenset(adj) if root_scope is None else root_scope
    balls = {u: frozenset(v for v, d in distances(adj, allowed, u).items() if d <= k)
             for u in allowed}
    keys = {balls[u] & balls[v] for u in allowed for v in allowed}
    assert len(keys) <= len(allowed)**2
    critical = {}
    for scope in sorted(keys, key=len):
        committed, equal = 0, []
        for u in scope:
            child = scope & balls[u]
            assert child in keys
            if child == scope:
                equal.append(threshold[u])
            else:
                committed += threshold[u] <= critical[child]
        critical[scope] = next(i for i in range(committed + len(equal), -1, -1)
                               if committed + sum(t <= i for t in equal) >= i)
    return {u: threshold[u] <= critical[balls[u]] for u in allowed}


def main():
    rng = Random(455652)
    tests = 0
    for n in range(1, 17):
        for rep in range(34):
            adj = {u: set() for u in range(n)}
            for u in range(1, n):
                v = 0 if rep == 0 else (u-1 if rep == 1 else rng.randrange(u))
                adj[u].add(v)
                adj[v].add(u)
            allowed = frozenset(adj)
            k = rng.randrange(n+2)
            threshold = [rng.randrange(n+3) for u in range(n)]
            ar = dp(adj, k, threshold)
            for u in adj:
                view = frozenset(v for v,d in distances(adj, allowed, u).items() if d <= k)
                assert ar[u] == ref(adj, k, threshold, u, view)
                assert ar[u] == dp(adj, k, threshold, view)[u]
                tests += 1
    print(f"{tests} rooted comparisons on 544 finite trees; all agree.")

if __name__ == '__main__':
    main()
