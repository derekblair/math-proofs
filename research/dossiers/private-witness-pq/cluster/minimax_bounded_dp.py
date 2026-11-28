"""Exact maximum over fixed-wire disjoint layouts with G groups.
For a claimed survival level x, an adversary needs a sum of inverse
piecewise-linear exposure levels to bring all group payoffs down to x.
A size-composition DP verifies the best layout globally at that x.
"""
from fractions import Fraction as Q
from math import comb, lcm
from functools import cache

N=130; C=63; F=6; R=7
Z=Q(0); O=Q(1)
@cache
def survival(n):
 d=comb(n,R)
 return tuple(Q(comb(n-e,R),d) for e in range(n-R+2))
@cache
def inverse(n,x):
 s=survival(n)
 if x==0:return Q(len(s)-1)
 a,b=0,len(s)-1
 while b-a>1:
  mid=(a+b)//2
  if s[mid]>=x:a=mid
  else:b=mid
 return a+(s[a]-x)/(s[a]-s[b])

def level(L):
 bp=sorted(set().union(*(survival(n) for n in L)))
 def total(x):return sum(inverse(n,x) for n in L)
 l,h=0,len(bp)-1
 while h-l>1:
  m=(l+h)//2
  if total(bp[m])>=C:l=m
  else:h=m
 lo,hi=bp[l],bp[h]
 sl,sh=total(lo),total(hi)
 return lo+(hi-lo)*(sl-C)/(sl-sh)

def maximize_at(g,x,Lmax):
 top=Lmax-(g-1)*R
 v={n:inverse(n,x) for n in range(R,top+1)}
 scale=lcm(*(p.denominator for p in v.values()))
 v={n:p.numerator*(scale//p.denominator) for n,p in v.items()}
 dp={0:(0,())}
 for j in range(g):
  next={}
  for tot,(score,L) in dp.items():
   if j+1==g: choices=range(max(R,C+1+g*F-tot),Lmax-tot+1)
   else: choices=range(R,Lmax-tot-(g-j-1)*R+1)
   for n in choices:
    z=tot+n; w=score+v[n]
    if z not in next or w>next[z][0]:next[z]=(w,L+(n,))
  dp=next
 s,L=max(dp.values())
 return Q(s,scale),tuple(sorted(L))

def main():
 for g in range(1,(N-C-1)//F+1):
  cap=min(N,88+g*F)
  layout=tuple(sorted((R,)*(g-1)+(cap-(g-1)*R,)))
  x=level(layout)
  i=0
  while True:
   i+=1
   m,L=maximize_at(g,x,cap)
   assert m>=C
   if m==C:break
   xx=level(L)
   assert xx>x
   layout=L;x=xx
  assert sum(inverse(n,x) for n in layout)==C
  prev=1/x
  print(g,'decaps',sum(layout)-g*F,'wire',sum(layout),'loss',float(28*prev),'layout',layout,
    'exact lambda',x,'iterations',i,flush=True)
if __name__=='__main__':main()
