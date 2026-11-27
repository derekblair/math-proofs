"""Find and check C64 in the second mod-3 homology cover of Heawood."""
from collections import defaultdict
chords=[(2,10),(3,11),(4,11),(4,12),(5,12),(5,13),(6,9),(6,13)]
powers={e:3**k for k,e in enumerate(chords)}
def nxt(v,c):
    u,a=v;d=(0,1,3)[c]
    w=7+(u+d)%7 if u<7 else (u-7-d)%7
    q=powers.get(tuple(sorted((u,w))))
    if q:
      h=a//q%3
      a+=q*((h+(1 if u<7 else -1))%3-h)
    return w,a
root=(0,0)
data=[defaultdict(list) for _ in range(3)]
def explore(i,vs,w):
    L=len(w)
    if L and L%2==0:
       data[w[0]][(i,L)].append((frozenset(vs[1:-1]),w))
    if L==16:return
    for c in range(3):
        if w and c==w[-1]:continue
        j=nxt(i,c)
        if j not in vs:explore(j,vs+(j,),w+(c,))
explore(root,(root,),())
def theta():
    for (v,l),xs in data[0].items():
        for m in range(2,17,2):
            n=32-l-m
            if n<2 or n>16 or n%2:continue
            ys=data[1].get((v,m),()); zs=data[2].get((v,n),())
            if not ys or not zs:continue
            for A,X in xs:
                for B,Y in ys:
                    if A&B:continue
                    for C,Z in zs:
                        if not ((A|B)&C):return v,X,Y,Z
out=theta()
if not out: print('no theta');raise SystemExit
v,X,Y,Z=out
W=X+Y[::-1]+Z+X[::-1]+Y+Z[::-1]
i=root; d={};seen=set()
for c in W:
    s=(i,frozenset(d.items()));assert s not in seen;seen.add(s)
    j=nxt(i,c)
    forward=i[0]<7
    e=(i,j) if forward else (j,i)
    a=(d.get(e,0)+(1 if forward else -1))%3
    if a:d[e]=a
    else:d.pop(e,None)
    i=j
assert len(W)==len(seen)==64 and i==root and not d
print('junction',v,'paths',*[ ''.join(map(str,p)) for p in (X,Y,Z)])
print('C64', ''.join(map(str,W)))
