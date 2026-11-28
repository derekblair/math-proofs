"""Exact integer enumeration of exposures and structure. No crypto or live endpoints."""
from math import comb
from fractions import Fraction
from functools import cache
from itertools import combinations

@cache
def alloc(total,count,n,lo=0):
    if not count:
        return ((),) if total==0 else ()
    if total < lo*count or total > n*count:
        return ()
    return tuple((a,)+tail
                 for a in range(max(lo,total-(count-1)*n),min(n,total//count)+1)
                 for tail in alloc(total-a,count-1,n,a))

def esym(k,vals):
    vec=[1]+[0]*k
    for w in vals:
        for t in range(k,0,-1):vec[t]+=w*vec[t-1]
    return vec[-1]

def result(n,g,w,r,c):
    v=[comb(n-e,r) for e in range(n+1)]
    L=alloc(c,g,n)
    num,E=min((esym(w,[v[e] for e in A]),A) for A in L)
    return Fraction(num,comb(g,w)*comb(n,r)**w),E,len(L)

n,g,w,r,c=13,10,4,2,63
new,E,count=result(n,g,w,r,c)
assert new==Fraction(4963,1370928)
assert E==(6,)*7+(7,)*3
assert esym(4,[comb(n-e,r) for e in E])==28140210
old=Fraction(43,21220)
new_loss=2*2*w*r/new
old_loss=2*2*7/old
assert new_loss<old_loss
assert g*n==130 and (g-w+1)*(n-r+1)==84 and r*w>=7
print('allocations',count,'p',new,'minimum vector',E)
print('new family-agnostic multiplier',new_loss,float(new_loss))
print('existing comparable loss',float(old_loss),'new/old', float(new_loss/old_loss))
