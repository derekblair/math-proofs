from pathlib import Path
from contextlib import redirect_stdout
from io import StringIO
with redirect_stdout(StringIO()):
 exec(Path('reconnaissance_actual.py').read_text())
N=28
P=[[(d,next(k for k,w in enumerate(W) if not collision(w,*v,*d)))for d in [(0,1)]+[(1,q)for q in range(v[0])]]for v in bad]
def ints(c,dir,k):
 p,a,b=c
 r,w,_=W[k];u,v=(1,0),(0,0);out=[]
 t=[int(a==1),int(a!=1)]
 da,db=dir;A=[(a,da),(b,db)]
 A0=[pow(a,-1,p),pow(b,-1,p)]
 Ai=[(A0[0],-da*A0[0]**2%p),(A0[1],-db*A0[1]**2%p)]
 def mul(x,y):return x[0]*y[0]%p,(x[0]*y[1]+x[1]*y[0])%p
 def add(x,y):return (x[0]+y[0])%p,(x[1]+y[1])%p
 def neg(x):return -x[0]%p,-x[1]%p
 def key(s,x,y):
  return p**4*s+p**3*x[0]+p**2*x[1]+p*y[0]+y[1]
 for d in w:
  out.append(key(r,u,v))
  if d=='2':r^=1
  elif d=='0':
   if t[r]:v=add(v,u)
   u=mul(u,A[r])
  else:
   u=mul(u,Ai[r])
   if t[r]:v=add(v,neg(u))
 assert u==(1,0) and v==(0,0) and r==W[k][0]
 return out+[key(r,u,v)]
def ar(a):return '#['+','.join(map(str,a))+']'
S='''import RibbonOddJetTable
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
for i in range(N):
 S+=f'def storedRows{i} : Array (Array Nat) := '+ar(ar(ints(bad[i],d,k))for d,k in P[i])+'\n'
S+='def jetBank : Array (Array (Array Nat)) := '+ar('storedRows'+str(i)for i in range(N))+'\n'
S+='''def storedJet (i : Fin 28) (d : Dir i) : Array Nat := (jetBank[i.val]!)[d.val]!
def jetBankOk (i : Fin 28) (d : Dir i) : Prop :=
  let k := pickJet i d
  let row := direction i d
  jetRow i row.1 row.2 k=storedJet i d
instance (i : Fin 28) (d : Dir i) : Decidable (jetBankOk i d) := by unfold jetBankOk; infer_instance

def jetFastOk (i : Fin 28) (d : Dir i) : Prop :=
  let k := pickJet i d
  RibbonP11Pair.checkRows (storedJet i d) (storedJet i d) (spec k)=true
instance (i : Fin 28) (d : Dir i) : Decidable (jetFastOk i d) := by unfold jetFastOk; infer_instance
end RibbonOddFinite
'''
Path('RibbonOddJetBank.lean').write_text(S)
mods=['RibbonOddJetBank']
for a in range(0,N,2):
 nm=f'RibbonOddJetBankCheck{a//2}';mods.append(nm)
 s='''import RibbonOddJetBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
 for i in range(a,min(N,a+2)):
  s+=f'theorem verifyJetBank{i} : ∀ d : Dir {i}, jetBankOk {i} d := by decide +kernel\n'
  s+=f'theorem verifyJetFast{i} : ∀ d : Dir {i}, jetFastOk {i} d := by decide +kernel\n'
 s+='end RibbonOddFinite\n'
 Path(nm+'.lean').write_text(s)
nm='RibbonOddJetPacked';mods.append(nm)
s='\n'.join('import '+m for m in mods[1:-1])+'''
namespace RibbonOddFinite
open RibbonStationaryWord RibbonOrderThree
theorem jet_bank_verified (i : Fin 28) (d : Dir i) : jetBankOk i d := by
  fin_cases i
'''
s+=''.join(f'  · exact verifyJetBank{i} d\n'for i in range(N))
s+='''theorem jet_fast_verified (i : Fin 28) (d : Dir i) : jetFastOk i d := by
  fin_cases i
'''
s+=''.join(f'  · exact verifyJetFast{i} d\n'for i in range(N))
s+='''theorem jets_checked (i : Fin 28) (d : Dir i) : checkJet i d := by
  have h := jet_fast_verified i d
  have e := jet_bank_verified i d
  unfold jetFastOk at h
  unfold jetBankOk at e
  rw [←e] at h
  exact h

end RibbonOddFinite
#print axioms RibbonOddFinite.jets_checked
'''
Path(nm+'.lean').write_text(s)
Path('jet_bank.order').write_text('RibbonOddJetTable '+' '.join(mods)+'\n')
print('applicable row checks',sum(map(len,P)))
