"""Exact free reduction and cyclic conjugacy for two signed letters."""
def fw(w,side=0):
 out=[]
 for p in w:
  if p=="2":side^=1
  else:out.append((side+1)*(1 if p=="0" else -1))
 return tuple(out)
def inv(w):return tuple(-x for x in w[::-1])
def red(w):
 out=[]
 for x in w:
  if out and out[-1]==-x:out.pop()
  else:out.append(x)
 return tuple(out)
def cr(w):
 w=red(w);p=()
 while w and w[0]==-w[-1]:p+=w[:1];w=w[1:-1]
 return p,w
def mat(a,b):
 p,u=cr(a);q,v=cr(b)
 for j in range(len(v)):
  if v[j:]+v[:j]==u:
   t=red(p+inv(v[:j])+inv(q))
   assert red(t+b+inv(t))==red(a)
   return t
