"""Exact upper bound on the specific old-theorem parameter family (not a runtime lower bound)."""
from fractions import Fraction as F
from functools import lru_cache
from rational_intervals import *
L=log(2)
F5=log(5)
goal=F(".0003737")
T=F(1,100)
@lru_cache(None)
def cvals(c):
    base=add(sub(sub(mul(box(c),F5),mul(box(c/2),H(1/c))),mul(box(c-1),L)),box(0))
    return div(log((c-1)/4),L),base
@lru_cache(None)
def qvalue(t):
    if not t: return box(0)
    return div(add(H(t),mul(box(t),log(4))),L)
assert qvalue(T)[0]>F(1,12)
# For c>=128, H(1/c)<=ln2, giving B(c)>=c*(ln5-3/2 ln2).
# ln(c/4)/c decreases there; use gamma/2 as the active upper bound.
tail=div(mul(box(T/2),log(32)),mul(box(128),sub(F5,mul(box(F(3,2)),L))))
assert tail[1]<goal
count=0; stack=[(F(5),F(128),F(0),T)]; accepted=0; max_accepted=F(0)
while stack:
    a,b,s,t=stack.pop();count+=1
    g1,base=cvals(a)
    gu=cvals(b)[0][1]*t
    gl=g1[0]*s
    ql=qvalue(s)[0]
    rz=div(L,add(box(base[0]),mul(box(gl),L)))[1]
    ub=rz*min(gu/2,(1-12*ql)/14)
    if ub<=goal:
        accepted+=1;max_accepted=max(max_accepted,ub);continue
    if (b-a)/(a+1)>90*(t-s):
        m=(a+b)/2;stack.extend([(a,m,s,t),(m,b,s,t)])
    else:
        m=(s+t)/2;stack.extend([(a,b,s,m),(a,b,m,t)])
    assert count<500000, "roundoff or invalid target"
print("exact branch-and-bound boxes:",count,"terminal:",accepted,"upper:",float(max_accepted))
