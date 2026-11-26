from symbolic_d2 import *
from ast import literal_eval
from pathlib import Path
lines=Path(__file__).with_name('residual-frozen.log').read_text().splitlines()
S=literal_eval(next(l[l.index('['):] for l in lines if l.startswith('all field residuals')))
T=literal_eval(next(l[l.index('['):] for l in lines if l.startswith('unsolved normalized')))
GOOD=sorted(set(S)-set(T))
def aff(p,a,b,r,w):
 ai=pow(a,-1,p);bi=pow(b,-1,p);u=1;v=0;out=[]
 for z in w:
  out.append((r,u,v))
  if z=='2':r^=1
  elif not r:u=u*(a if z=='0' else ai)%p
  elif z=='0':v=(v+u)%p;u=u*b%p
  else:u=u*bi%p;v=(v-u)%p
 return out
def hit(p,a,b,r,w,M):
 S=aff(p,a,b,r,w)
 return not any((i,j)not in M and S[i]==S[j] for j in range(64) for i in range(j))
X=[int(l.split()[0]) for l in open('all_forms.log')]
base=[0,1,2,4,5,6,16,18,145,146,150,151,158,161,174,184,182,203,28,194]
for p,a,b in GOOD:
 L=[j for j in base if hit(p,a,b,*W[j])]
 if not L:L=[j for j in X if hit(p,a,b,*W[j])]
 print(p,a,b,L[:10])
