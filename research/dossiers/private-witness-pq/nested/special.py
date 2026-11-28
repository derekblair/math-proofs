"""Exact two-mode certificate for one 13-of-13 cluster."""
from check_nested import alloc,esym
from fractions import Fraction as F
from itertools import product
from math import comb,lcm

D0=comb(9,4)*comb(13,2)**4
D1=13*comb(9,3)*comb(13,2)**3
D=lcm(D0,D1)
Q=[]
for e in range(14):
 for E in alloc(63-e,9,13):
  vals=[comb(13-h,2) for h in E]
  A=esym(4,vals)*(D//D0)
  B=(13-e)*esym(3,vals)*(D//D1)
  # A,B are exact endpoint probabilities times common denominator.
  Q.append((A,B,E,e))

def minimizer(q):
 p,d=q.numerator,q.denominator
 return min(Q,key=lambda z:(d-p)*z[0]+p*z[1])

a=minimizer(F(51728,100000)); b=minimizer(F(51729,100000))
A,B,_,_=a
C,E,_,_=b
assert (8*(B-A)+A)>0 and (8*(E-C)+C)<0
q=F(C-A,(B-A)-(E-C))
w=minimizer(q)
p=F((1-q)*w[0]+q*w[1],D)
assert p==F((1-q)*A+q*B,D)==F((1-q)*C+q*E,D)
assert q==F(5077873,9816373) and p==F(106948625,24647510264)
assert 4*(8-q)/p==F(5164047515744,748640375)
# Each active affine upper bound divided by (8-q) is monotone
# in opposite directions. Their crossing certifies the global maximum.
print('allocations',len(Q),'q',q,float(q),'p',p,float(p))
print('active left/right',a,b,'avg hybrid support',8-q)
print('multiplier for 2 families',4*(8-q)/p,float(4*(8-q)/p))
