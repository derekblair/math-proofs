"""Independent finite replay for both small-color thresholds."""
from itertools import product

def matchings(b, c):
    def grow(i, available):
        if i == b:
            yield frozenset()
        else:
            yield from grow(i+1, available)
            for j in available:
                for rest in grow(i+1, available - {j}):
                    yield rest | {(i,j)}
    return list(grow(0, set(range(c))))

def encode(b,c, M, N):
    adjacent=[[] for _ in range(b+c)]
    for z,E in enumerate((M,N)):
        for i,j in E:
            adjacent[i].append((b+j,z))
            adjacent[b+j].append((i,z))
    ids={}
    sizes=[];cycs=[]
    for i in range(b+c):
        if i in ids: continue
        t=len(sizes)
        ids[i]=t
        got=[i]
        for q in got:
            for j,_ in adjacent[q]:
                if j not in ids:
                    ids[j]=t
                    got.append(j)
        sizes.append(got)
        if all(len(adjacent[j])==2 for j in got):cycs.append(len(got)//2)
    m=max([b+c+1] if not cycs else cycs)
    for t,got in enumerate(sizes):
        start=got[0]
        val={start:0}; scan=[start]
        for q in scan:
            for j,z in adjacent[q]:
                a=(z-val[q])%m
                if j in val:
                    if val[j]!=a: return False
                else:
                    val[j]=a
                    scan.append(j)
        sizes[t]=val
    for i,j,z in product(range(b),range(c),range(2)):
        t=ids[i]; u=ids[j+b]
        actual=t==u and (sizes[t][i]+sizes[u][j+b])%m==z
        if actual != ((i,j) in (M,N)[z]): return False
    return True

cnt=0
for b,c in product(range(8),repeat=2):
    if b+c>7:continue
    ms=matchings(b,c)
    for M,N in product(ms,repeat=2):
        if M & N:continue
        assert encode(b,c,M,N),(b,c,M,N)
        cnt+=1
print("All",cnt,"labeled two disjoint matching instances with b+c<=7 encoded exactly.")
assert not encode(4,4,{(0,0),(1,1),(2,2),(3,3)},{(0,1),(1,0),(3,2)})
print("10-point threshold contrast: C4 plus 3-edge path.")
