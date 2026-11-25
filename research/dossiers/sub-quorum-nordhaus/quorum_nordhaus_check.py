"""Independent search over partial set partitions, using the closed majority definition."""
from functools import lru_cache
from itertools import combinations
from random import Random


@lru_cache(None)
def candidates(n):
    out = []
    def gen(i, blocks):
        if i == n:
            out.append((sum(blocks), tuple(blocks)))
            return
        gen(i+1, blocks)
        bit = 1 << i
        for j, b in enumerate(blocks):
            blocks[j] = b | bit
            gen(i+1, blocks)
            blocks[j] = b
        blocks.append(bit)
        gen(i+1, blocks)
        blocks.pop()
    gen(0, [])
    return sorted(out, key=lambda x: -len(x[1]))


def optimum(n, open_neighbors):
    closed = [(1<<i) | v for i,v in enumerate(open_neighbors)]
    for support, blocks in candidates(n):
        ok = True
        for b in blocks:
            scan = b
            while scan:
                bit = scan & -scan
                scan ^= bit
                ns = closed[bit.bit_length()-1]
                if 2*(ns & b).bit_count() < (ns & support).bit_count():
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return len(blocks)
    raise AssertionError("empty coloring is always feasible")


def test(n, mask):
    neighbors = [0]*n
    for j, (a,b) in enumerate(combinations(range(n),2)):
        if mask>>j&1:
            neighbors[a] |= 1<<b
            neighbors[b] |= 1<<a
    others = [((1<<n)-1) ^ (v | (1<<i)) for i,v in enumerate(neighbors)]
    s = optimum(n,neighbors)+optimum(n,others)
    assert s <= n+2
    if not mask and n >= 2:
        assert s == n+2


def main():
    rng = Random(109177)
    exact = randomized = 0
    for n in range(2,6):
        for mask in range(1<<(n*(n-1)//2)):
            test(n,mask)
            exact += 1
    for n in range(6,10):
        for mask in [0]+[rng.getrandbits(n*(n-1)//2) for _ in range(19)]:
            test(n,mask)
            randomized += 1
    print(f"{exact} labeled graphs checked exhaustively by order, and {randomized} larger examples.")

if __name__ == '__main__':
    main()
