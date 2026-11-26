from cover import *
from ast import literal_eval
from json import loads
from pathlib import Path
L=loads(Path('slope-integer.json').read_text())
C=[0,1,2,4,5,6,16,18,145,146,150,151,158,161,174,184,182,203]
def fmt(P):return list(map(int,reversed(P.all_coeffs()))) if not P.is_zero else []
def li(x):return '['+','.join(map(str,x))+']'
def ar(x):return '#'+li(x)
def pol(P):return li(f'({i},0,{c})' for i,c in enumerate(P) if c)
def const(n):return f'[(0,0,{n})]'
def ide(A,B,C,D,R):return '⟨'+','.join([pol(A),pol(B),pol(C),pol(D),pol(R)])+'⟩'
for subset in range(10):
 lo=subset*8; rr=L[lo:lo+8]
 data=[]
 for u,v,f,q,rows in rr:
  S=ar(f'⟨{d},{pol(g)},⟨{n},{ide(A,B,C,[],[n])}⟩⟩' for d,g,n,A,B,C in rows)
  keys={(d,tuple(g)):i for i,(d,g,*_) in enumerate(rows)}
  xrows=[[0 for _ in range(64)] for _ in range(64)]
  for i,j,a,b,H in pairs(W[q]):
   D=abs(a*v-b*u);d=remove23(D)
   u2,v3=0,0
   while D and D%2==0:u2+=1;D//=2
   while D and D%3==0:v3+=1;D//=3
   assert D==d
   P=Counter()
   for (x,y),c in H.items():P[x*v-y*u]+=c
   sh=-min((i for i,h in P.items() if h),default=0)
   fd=tuple(fmt(Poly(sum(c*t**(i+sh) for i,c in P.items() if c),t)))
   if d==1:xrows[i][j]=2+u2+8*v3
   else:xrows[i][j]=66+keys[d,fd]+64*u2+512*v3+4096*(sh+32)
   assert 0<=xrows[i][j]<262144
  for i,j in W[q][2]:xrows[i][j]=1
  A=ar(hex(sum(a*(262144**i) for i,a in enumerate(z)))for z in xrows)
  data.append(f'⟨{C.index(q)},{S},{A}⟩')
 dest=Path(f'RibbonStationarySlopeData{subset}.lean')
 dest.write_text(f'''import RibbonStationarySlopeCover
namespace RibbonStationaryField
open RibbonStationaryWord
set_option maxHeartbeats 0
set_option maxRecDepth 30000
def data{subset} : Array Cover := #[\n'''+',\n'.join(data)+f''']
theorem valid{subset} (k : Fin {len(rr)}) : RowValid (branch ({lo}+k.val)).p data{subset}[k.val]! := by
  fin_cases k <;> decide +kernel
theorem geom{subset} (k : Fin {len(rr)}) : GeomValid (branch ({lo}+k.val)) data{subset}[k.val]! := by
  fin_cases k <;> decide +kernel
end RibbonStationaryField
''')
