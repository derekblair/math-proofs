from simple import *
from itertools import product
WORDS=[
"0212121212002021202021121120200202121202121120202020212112120020",
"1202020202112120212120020021211212020212020021212121202002021121",
"1212020202112120212020211202002112120212020021212120200211212002",
]
old=fw("21200212120212020021212120200211")
def info(W):
 A=W[:32];k=22;U,V=A[:k],A[k:]
 assert W==A+rev(V+U)
 assert chart(U)[-1][:3]==(0,0,0)
 T=W+rev(W[k:]+W[:k])
 candidates=[]
 for sx,sy,sw,e in product((1,-1),(1,-1),(False,True),(1,-1)):
  f=tuple((sx*(1+sw) if abs(v)==1 else sy*(2-sw))*(1 if v>0 else -1) for v in old)
  if e<0:f=inv(f)
  t=mat(fw(A),f)
  if t is not None:candidates.append((len(t),sx,sy,sw,e,t))
 l,sx,sy,sw,e,t=min(candidates)
 args=(sx*(1+sw),sy*(2-sw))
 return A,U,V,W,T,t,args,e
if __name__=='__main__':
 for W in WORDS:
  A,U,V,W,T,t,args,e=info(W)
  print("r-conj",t,args,e,"prefix",fw(U),"lengths",[len(A), len(W),len(T)])
