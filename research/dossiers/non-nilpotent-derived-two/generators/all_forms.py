from symbolic_d2 import *
from itertools import product
import sys
from word_primitives import fw,mat,inv,red
S=range(len(W))
for i in S:
 rim,w,m=W[i]; R=fw(w[:32],rim)
 base=fw(W[0][1][:32], W[0][0]);c=[]
 for sx,sy,sw,e in product((1,-1),(1,-1),(False,True),(1,-1)):
  f=tuple((sx*(1+sw) if abs(v)==1 else sy*(2-sw))*(1 if v>0 else -1) for v in base)
  if e<0:f=inv(f)
  t=mat(R,f)
  if t is not None:c.append((len(t),sx,sy,sw,e,t))
 # Rotate first half by tested balanced U and match exact second reversed half
 def rev(w):return w[::-1].translate(str.maketrans('01','10'))
 u=[k for k in range(1,32) if w[32:]==rev(w[k:32]+w[:k]) and
      w[:k].count('2')%2==0 and all(fw(w[:k],rim).count(l)==fw(w[:k],rim).count(-l) for l in (1,2))]
 if c and u and rim==0:print(i,rim,min(c),u,len(m))
