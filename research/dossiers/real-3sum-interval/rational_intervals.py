"""Exact rational interval proof of all strict log inequalities used."""
from fractions import Fraction as F
def box(a):
    a=F(a)
    return a,a
def add(x,y): return x[0]+y[0],x[1]+y[1]
def neg(x): return -x[1],-x[0]
def sub(x,y): return add(x,neg(y))
def mul(x,y):
    v=[a*b for a in x for b in y]
    return min(v),max(v)
def div(x,y):
    assert y[0]>0
    return mul(x,(1/y[1],1/y[0]))
def logsmall(x,N=15):
    assert 1<=x<=2
    z=(x-1)/(x+1)
    v=2*sum((z**(2*j+1)/F(2*j+1) for j in range(N)),F(0))
    tail=2*z**(2*N+1)/(F(2*N+1)*(1-z*z))
    return v,v+tail
def log(x):
    x=F(x)
    k=0
    while x>2: x/=2; k+=1
    while x<1: x*=2; k-=1
    return add(logsmall(x),mul(box(k),logsmall(F(2))))
def H(x): return neg(add(mul(box(x),log(x)),mul(box(1-x),log(1-x))))
