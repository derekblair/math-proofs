from fractions import Fraction
from math import comb,lcm

def formulas(t,u):
 n=t+u+3
 w=[Fraction(1,comb(n,k)) for k in range(n+1)]
 C=sum(comb(3,j)*w[t+j] for j in range(4))
 L=w[t]+(u+3)*w[t+1]+(u+2)*w[t+2]
 H=w[t+3]+(t+3)*w[t+2]+(t+2)*w[t+1]
 return n,w,C,L,H

def brute(t,u):
 n,w,*_=formulas(t,u)
 V=sorted((x for x in range(1<<n) if t<=x.bit_count()<=t+3),
          key=lambda x:(-w[x.bit_count()],x))
 D=lcm(*(f.denominator for f in w))
 N=[0]*len(V);weights=[int(D*w[x.bit_count()]) for x in V]
 for i,x in enumerate(V):
  N[i]=sum(1<<j for j,y in enumerate(V)
           if i!=j and (x&y).bit_count()>=t and (x|y).bit_count()<=n-u)
 best=0; nodes=0
 def rec(P,val):
  nonlocal best,nodes
  nodes+=1
  best=max(best,val)
  left=P
  seq=[];caps=[];old=0
  while left:
   r=left;big=0
   while r:
    b=r&-r;i=b.bit_length()-1
    left^=b
    r&=~(b|N[i])
    seq.append(i);big=max(big,weights[i]);caps.append(old+big)
   old+=big
  for i,cap in zip(reversed(seq),reversed(caps)):
   if cap+val<=best:return
   rec(P&N[i],val+weights[i])
   P^=1<<i
 rec((1<<len(V))-1,0)
 return Fraction(best,D),nodes

for t in range(1,51):
 for u in range(t,51):
  n,w,c,l,h=formulas(t,u)
  assert (l-h)/w[t+1]==Fraction((t+2)*(u-t)*(t+u+4),(t+1)*(u+1))
  assert l>=h
  assert (l>c)==(u>=2)
for t in range(1,4):
 for u in range(t,7-t):
  n,w,c,l,h=formulas(t,u)
  if n>8:continue
  result,nodes=brute(t,u)
  assert result==max(c,l,h),(t,u,result,c,l,h)
  print(n,t,u,result,nodes)
