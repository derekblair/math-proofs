from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
from math import comb, prod, lcm
v=[comb(13-x,2) for x in range(14)]
def elementary(X,r):
    a=[1]+[0]*r
    for x in X:
        a=[1]+[a[j]+a[j-1]*x for j in range(1,r+1)]
    return a[-1]

def symmetric():
    best=10**12; count=0
    for E in combinations_with_replacement(range(14),10):
        if sum(E)!=63:continue
        count+=1
        best=min(best,elementary([v[x] for x in E],4))
    assert (count,best)==(27523,28140210)
    return F(best,comb(10,4)*78**4)

def asymmetric():
    a,b=comb(9,4)*78**4,13*comb(9,3)*78**3
    d=lcm(a,b)
    q=F(5077873,9816373)
    best=10**25; count=0; winners=set()
    for E in combinations_with_replacement(range(14),9):
        s=63-sum(E)
        if not (0<=s<=13):continue
        count+=1
        X=[v[x] for x in E]
        price=(q.denominator-q.numerator)*elementary(X,4)*(d//a)+q.numerator*(13-s)*elementary(X,3)*(d//b)
        if price<best: best=price; winners=set()
        if price==best: winners.add((s,E))
    assert count==174261
    assert winners=={(0,(7,)*9),(13,(5,)*4+(6,)*5)}
    return F(best,d*q.denominator)
print(symmetric(),asymmetric())
