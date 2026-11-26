from itertools import combinations, product
from collections import Counter

# Vertices 0,1,2 are minus, 3,4,5 plus; edge (u,v) oriented minus to plus.
edges=tuple(product(range(3),range(3,6)))
tree={(0,3),(0,4),(0,5),(1,3),(2,3)}
cotree=tuple(e for e in edges if e not in tree)
zero=(0,0,0,0)
def adj(u,j):
    return 3+(u+j)%3 if u<3 else (u-3-j)%3
def step(state,j,p):
    u,a=state; v=adj(u,j); e=(min(u,v),max(u,v))
    if e not in tree:
        k=cotree.index(e); a=a[:k]+((a[k]+(1 if u<3 else -1))%p,)+a[k+1:]
    return v,a
def words(n, root, p):
    stack=[((),(root,zero))]
    for _ in range(n):
        stack=[(L+(j,),step(s,j,p)) for L,s in stack for j in range(3) if not L or j!=L[-1]]
    return stack
def cycle(n,root,p):
    ends={}
    for w,s in words(n//2,root,p):
        for v in ends.setdefault(s,[]):
            W=w+v[::-1]
            a=(root,zero); seen={a}
            for j in W:
                a=step(a,j,p)
                if a in seen:break
                seen.add(a)
            if len(seen)==n and a==(root,zero):return ''.join(map(str,W))
        ends[s].append(w)

def paths(u,v,seen=()):
    for j in range(3):
        w=adj(u,j)
        if w==v:yield (u,v)
        elif w not in (u,*seen):
            yield from ((u,*path) for path in paths(w,v,seen+(u,)))
def theta_census(p):
    out=Counter()
    for u,v in combinations(range(6),2):
        for arms in combinations(paths(u,v),3):
            if sum(len(a)-2 for a in arms)!=len(set(k for a in arms for k in a[1:-1])):continue
            d=[]
            for a in arms:
                s=(u,zero)
                for q,r in zip(a,a[1:]):
                    s=step(s,next(j for j in range(3) if adj(q,j)==r),p)
                d.append(s[1])
            out[tuple(sorted(len(a)-1 for a in arms)),len(set(d))]+=1
    return out
if __name__=='__main__':
    for p in (3,5,7):
        print(p,theta_census(p),[(n,cycle(n,0,p)) for n in (4,8,16,32)])
