from symbolic_d2 import *
from collections import Counter
from itertools import accumulate
def S(w):
 x=y=0;out=[]
 for z in w:
  d=1 if z>0 else -1
  if abs(z)==1:
   if y:out.append((x+min(d,0),y,d))
   x+=d
  else:y+=d
 assert x==y==0
 return out
if __name__=='__main__':
 import sys
 from word_primitives import fw
 for j in (145,150):
  r,w,m=W[j]
  L=S(fw(w[:32],r)); F=Counter()
  for x,y,d in L:F[x,y]+=d
  print(j,w, len(m),'S',L,'balanced',not any(F.values()))
