from functools import lru_cache
from math import comb

def pattern(h):
    out=[]
    for i in range(3*h+1):
        q,r=divmod(i,3)
        out.append(3*q+(0,3*(1-h)+1,3*h+2)[r])
    ix={v:i for i,v in enumerate(sorted(out))}
    return [ix[v] for v in out]

def literal(p,step,j):
    N=len(p)+(j-1)*step
    pred=[0]*N
    for t in range(j):
        for x in range(len(p)):
            for y in range(len(p)):
                if p[x]<p[y]:
                    pred[step*t+y]|=1<<(step*t+x)
    @lru_cache(None)
    def walk(rest):
        if rest==0:return 1
        val=0; choices=rest
        while choices:
            b=choices&-choices
            choices^=b
            if not pred[b.bit_length()-1]&rest:
                val+=walk(rest^b)
        return val
    return walk((1<<N)-1)

def simple(h,j):
    an=h+j
    bn=cn=an-1
    @lru_cache(None)
    def f(a,b,c):
        if (a,b,c)==(an,bn,cn):return 1
        n=0
        if a<an and b>=min(a,j)+h-1:n+=f(a+1,b,c)
        if b<bn and a>=b-h+2:n+=f(a,b+1,c)
        if c<cn and a>=min(c,j-1)+h+1:n+=f(a,b,c+1)
        return n
    return f(0,0,0)

C=lambda j:comb(2*j,j)//(j+1)
A=[0,2,1,3]
B=pattern(5)
assert B==[4,0,11,6,1,12,7,2,13,8,3,14,9,5,15,10]
AA=[literal(A,2,j) for j in range(1,7)]
BB=[literal(B,3,j) for j in range(1,7)]
assert AA==[1,2,5,14,42,132]
assert BB==[1,2,5,14,42,174]
print('Literal all-pairs per-window counts:')
print('1-based first pattern:', [x+1 for x in A], 'overlap 2:', AA)
print('1-based second pattern:', [x+1 for x in B], 'overlap 13:', BB)
tests=0
for h in range(2,15):
    p=pattern(h)
    for j in range(1,min(9,h+3)):
        assert literal(p,3,j)==simple(h,j),(h,j,literal(p,3,j),simple(h,j))
        tests+=1
for h in range(2,45):
    for j in range(1,h+1):
        assert simple(h,j)==C(j)
    assert simple(h,h+1)==C(h+1)+C(h)
print(tests,'row-path comparisons pass; general-delay candidate numerically matches h=2..44')
