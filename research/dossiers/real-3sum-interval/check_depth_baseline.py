"""Exact rational interval checker; no imports from the candidate's scripts."""
from fractions import Fraction as F
from decimal import Decimal, localcontext

def point(v):
    v=F(v)
    return v,v
def plus(a,b): return a[0]+b[0],a[1]+b[1]
def times(a,b):
    p=[x*y for x in a for y in b]
    return min(p),max(p)
def negate(a): return -a[1],-a[0]
def minus(a,b): return plus(a,negate(b))
def divide(a,b):
    assert b[0]>0
    return times(a,(1/b[1],1/b[0]))
def shortlog(x,k=18):
    assert 1<=x<=2
    z=(x-1)/(x+1)
    prefix = sum((2*z**(2*j+1)/F(2*j+1) for j in range(k)),F(0))
    remainder = 2*z**(2*k+1)/(F(2*k+1)*(1-z*z))
    return prefix,prefix+remainder
def log(x):
    x=F(x); k=0
    while x<1:
        k-=1; x*=2
    while x>2:
        k+=1; x/=2
    return plus(shortlog(x),times(point(k),shortlog(F(2))))
def H(x):
    return negate(plus(times(point(x),log(x)),times(point(1-x),log(1-x))))

A=[('7.86328','.00739224'),('8.29078','.00739777'),('8.74480','.00740331'),
   ('9.22697','.00740886'),('9.73905','.00741441'),('10.28286','.00741997'),
   ('10.86036','.00742555'),('11.47367','.00743112')]
delta=F('.06222')
alpha=F('.006065')
l2=log(2)

def box_rate(c,t):
    theta_term=H((1-t)/c)
    zero_term=H(1/c)
    return minus(divide(times(point(c),minus(zero_term,theta_term)),l2),point(2*t))

def verify():
    for i,(cs,ts) in enumerate(A):
        c,t=F(cs),F(ts)
        assert c>5 and 0<t<F('0.8')
        gamma=box_rate(c,t)
        q=divide(plus(H(t),times(point(t),log(4))),l2)
        rad_denom=plus(minus(minus(times(point(c),log(5)),times(point(c/2),H(1/c))),
                           times(point(c-1),l2)),times(gamma,l2))
        rad=divide(l2,rad_denom)
        P=12+delta-i*delta/8
        eta=(i+1)*delta/8
        margins=[minus(times(point(P),gamma),point(delta+eta)),
                 minus(point(1-delta),times(point(P),q)),minus(rad,point(alpha*P))]
        assert min(m[0] for m in margins)>0
        print(i, *(f'{float(m[0]):.10g}' for m in margins))
    assert 2-alpha*delta < F('1.9996227')
    print('exact gap',alpha*delta,'raw exponent',float(2-alpha*delta))

if __name__=='__main__': verify()
