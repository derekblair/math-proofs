"""Half-word collision screen for metabelian odd-order wreath examples."""
from itertools import product
from collections import defaultdict
def check(m,b,p,n,ranktwo=False, witness=False):
    s=(0,0) if ranktwo else 0
    deltas=((0,0),(1,0),(0,1)) if ranktwo else (0,1,b)
    def move(s,d,i):
        if ranktwo:return tuple((x+i*y)%m for x,y in zip(s,d))
        return (s+i*d)%m
    buckets=defaultdict(list); word=[]
    def rec(s,v,j):
        i=len(word)
        if i==n:
            k=s,tuple(sorted(v.items()))
            for row in buckets[k]:
                if row[0]!=word[0] and row[-1]!=word[-1]:return row+tuple(word[::-1])
            buckets[k].append(tuple(word))
            return None
        fw=1 if i%2==0 else -1
        for c,d in enumerate(deltas):
            if c==j:continue
            ss=move(s,d,fw); key=(c,s if fw==1 else ss)
            old=v.get(key,0)
            if c:
                new=(old+fw)%p
                if new:v[key]=new
                else:v.pop(key,None)
            word.append(c);w=rec(ss,v,c);word.pop()
            if c:
                if old:v[key]=old
                else:v.pop(key,None)
            if w:return w
        return None
    return rec(s,{},-1)
for m in [7,9,11,13,15,17,19,21]:
    for b in range(2,m):
        first=next(((2*n, w) for n in range(2,12) if (w:=check(m,b,5,n))),None)
        if first is None or first[0]>=22:
            print('cyclic found',m,b,first);break
    else:continue
    break
for m in [5,7,9]:
    first=next(((2*n, w) for n in range(2,12) if (w:=check(m,0,5,n,True))),None)
    print('ranktwo',m,first)
