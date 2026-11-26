from symbolic_d2 import *
from schreier import S
import sys, ast
from word_primitives import fw,mat,inv,red
def elt(p):return {1:0,-1:1,2:2,-2:3}[p]
def l(w):return '['+','.join(map(str,w))+']'
def lt(w):return l(map(elt,w))
def v(w):return '#'+l(w)
def vp(w):return '#'+l(w)
def rev(w):return w[::-1].translate(str.maketrans('01','10'))
def sci(i,j):return (1 if i>=0 else -1,)*abs(i)+(2 if j>=0 else -2,)*abs(j)+(1,)+(2 if j<=0 else -2,)*abs(j)+(-1,)+(-1 if i>=0 else 1,)*abs(i)
def encode_s(L):return lt(sum((sci(i,j) if d>0 else inv(sci(i,j)) for i,j,d in L),()))
C=[0,1,2,4,5,6,16,18,145,146,150,151,158,161,174,184,182,203,28,194]
M={int(line.split()[0]):ast.literal_eval(line[line.index('('):line.index(') [')+1]) for line in open('all_forms.log')}
baseR=fw(W[0][1][:32],0)
OUT=[]; D=[]
for i in C:
 rim,w,m=W[i]; assert rim==0
 R=fw(w[:32],rim)
 k=next(k for k in range(1,32) if w[32:]==rev(w[k:32]+w[:k]) and
   w[:k].count('2')%2==0 and all(fw(w[:k],rim).count(j)==fw(w[:k],rim).count(-j) for j in (1,2)))
 U=fw(w[:k],0); u=S(U)
 cu=encode_s(u)
 F=fw(w,0)
 FS=fw(w[32:],0)
 assert red(F)==red(R+inv(U)+inv(R)+U)
 assert red(FS)==red(inv(U)+inv(R)+U)
 mates=[]
 for a,b in sorted(m):
  H=inv(fw(w[:a],0))+fw(w[:b],0)
  for isinv in (False,True):
   tr=mat(H,inv(R) if isinv else R)
   if tr is not None:break
  assert tr is not None
  mates.append(f'⟨{a},{b},{str(isinv).lower()},{lt(tr)}⟩')
 if i in (145,150):
  L=S(R)
  s1,s2=(L[:1],L[1:2]) if i==145 else (L[:2],L[2:4])
  rs=lambda q: l(f'({x},{y},{str(d<0).lower()})' for x,y,d in q)
  form=f'.single {rs(s1)} {rs(s2)}'
 else:
  _,sx,sy,sw,e,conj=M[i]
  form=f'.transport {elt(sx*(1+sw))} {elt(sy*(2-sw))} {str(e<0).lower()} {lt(conj)}'
 rs=lambda q: l(f'({x},{y},{str(d<0).lower()})' for x,y,d in q)
 D.append(f'⟨{i},{l(w)}, {k}, {rs(u)}, {form}, {v(mates)}⟩')
Path('RibbonAllOddWordData.lean').write_text('''import RibbonStationaryWordCore

namespace RibbonAllOddField
open RibbonStationaryWord (Spec Valid)
def words : Array Spec := #[\n  '''+',\n  '.join(D)+''']
abbrev Count := Fin '''+str(len(D))+'''
def spec (i : Count) := words[i.val]!
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem all_valid : ∀ i : Count, Valid (spec i) := by decide +kernel
end RibbonAllOddField
#print axioms RibbonAllOddField.all_valid
''')
