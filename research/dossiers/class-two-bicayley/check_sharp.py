#!/usr/bin/env python3
from itertools import product
P=3
def op(x,y):
    a,b,c=x; d,e,f=y
    return ((a+d)%P,(b+e)%P,(c+f+a*e)%P)
one=(0,0,0)
a,a_inv,b,b_inv=(1,0,0),(2,0,0),(0,1,0),(0,2,0)
def step(v,j):
    side,x=v
    return (1-side,x) if j==2 else (side,op(x,((a,a_inv),(b,b_inv))[side][j]))
def cycle(n,side):
    s=(side,one)
    stack=[(s,(s,),())]
    while stack:
        v,used,word=stack.pop()
        for j in range(3):
            w=step(v,j)
            if len(used)==n:
                if w==s: return word+(j,)
            elif w not in used:
                stack.append((w,used+(w,),word+(j,)))
print("graph vertices", 2*P**3)
for n in [3,4,8,16]:
    print(n,[cycle(n,side) for side in [0,1]])
assert cycle(3,0) is not None
assert all(cycle(n,side) is None for n,side in product((4,8),(0,1)))
assert cycle(16,0) is not None
