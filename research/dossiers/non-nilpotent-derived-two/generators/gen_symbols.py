from symbolic_d2 import *
from pathlib import Path
C=[0,1,2,4,5,6,16,18,145,146,150,151,158,161,174,184,182,203]
def li(a):return '['+','.join(map(str,a))+']'
def sym(w):
 r,p,_=w
 x=y=0;z=[];o=[]
 for d in p:
  o.append('⟨'+','.join([str(bool(r)).lower(),str(x),str(y),li(f'({i},{j},{k})'for i,j,k in z)])+'⟩')
  if d=='2':r^=1
  elif d=='0' and r:z.insert(0,(x,y,1));y+=1
  elif d=='1' and r:y-=1;z.insert(0,(x,y,-1))
  else:x+=1 if d=='0' else -1
 return '#'+li(o)
S=[sym(W[k]) for k in C]
p='''import RibbonStationaryBaseData
namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (Row)
set_option maxHeartbeats 0
set_option maxRecDepth 30000
def symData : Array (Array Row) := #[\n'''+',\n'.join(S)+''']
def sym (k : Count) (i : Fin 64) : Row := (symData[k.val]!)[i.val]!
theorem sym_ok : ∀ k : Count, ∀ i : Fin 64, sym k i= symbol k i.val := by decide +kernel
end RibbonStationaryField
'''
Path('RibbonStationarySymbols.lean').write_text(p)
