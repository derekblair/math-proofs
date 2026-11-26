from pathlib import Path
from collections import defaultdict,Counter
W="2020211211202002021212121200202120202121121200200212120212112020"
A=W[:32]; k=22; U=A[:k]; V=A[k:]
B=V+U
def rev(w):return w[::-1].translate(str.maketrans("01","10"))
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
def chart(w):
 s=x=y=c=0;out=[]
 for p in w:
  out.append((s,x,y,c))
  if p=="2":s^=1
  elif not s:x += 1 if p=="0" else -1
  else:
   d=1 if p=="0" else -1
   y+=d;c+=x*d
 return out+[(s,x,y,c)]
assert W==A+rev(B)
T=W+rev(W[k:]+W[:k])
def cl(a,b):return a+b+inv(a)+inv(b)
G=fw(A);Z=fw(W);P=fw(U)
assert chart(U)[-1][0:3]==(0,0,0)
assert red(Z)==red(cl(fw(U),fw(V)))
assert red(fw(T)) == red(cl(Z,inv(P)))
# Optional provenance cross-check; the deterministic generator needs no census.
source = Path('../flagship-class7-1700/balanced128.tsv')
if source.exists():
 assert (0,k,W,T) in [(int(b),int(j),w,t) for b,j,w,t in map(str.split,source.read_text().splitlines())]
vals={ (a,b):(G if a>0 else inv(G))*abs(a)+(Z if b>0 else inv(Z))*abs(b)
 for a,b in ((1,0),(-1,0),(0,1),(0,-1),(-1,1),(1,-1),(1,1),(-1,-1))}
def select(d):
 for k,w in vals.items():
  r=mat(d,w)
  if r is not None:return k,r
 raise ValueError(d)
def data(w):
 p=chart(w)[:-1]
 hi=[max(q[i] for q in p)-min(q[i] for q in p) for i in (1,2)]
 cnt=Counter(); matches=[]
 for j,q in enumerate(p):
  for i,r in enumerate(p[:j]):
   if q[:3]!=r[:3]:continue
   if q[3]!=r[3]:cnt[abs(q[3]-r[3])]+=1;continue
   matches.append((i,j,*select(inv(fw(w[:i]))+fw(w[:j]))))
 return hi,dict(sorted(cnt.items())),matches
if __name__=='__main__':
 print('A',A,'U',U,'V',V,'W',W,'T',T,sep='\n')
 old=fw('21200212120212020021212120200211')
 repl=lambda v: (2*(1 if v>0 else -1)) if abs(v)==1 else -(1 if v>0 else -1)
 old=tuple(map(repl,old));Rref=inv(old)
 print('U abelian exponents',chart(U)[-1])
 print('A conjugator old R(y,x^-1)^-1',mat(G,Rref))
 for w in (A,W,T):
  print(len(w),data(w))
