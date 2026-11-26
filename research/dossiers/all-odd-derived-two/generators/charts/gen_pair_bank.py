from pathlib import Path
from itertools import combinations
from contextlib import redirect_stdout
from io import StringIO
with redirect_stdout(StringIO()):
 exec(Path('reconnaissance_actual.py').read_text())
N=28
P={(i,j):next(k for k,R in enumerate(tab) if not(R[i]&R[j])) for i,j in combinations(range(N),2)}
used=[set()for _ in range(N)]
for (i,j),k in P.items():
 used[i].add(k);used[j].add(k)
def ints(c,k):
 p,a,b=c;r,w,_=W[k]
 A=[a,b];Ai=[pow(a,-1,p),pow(b,-1,p)]
 t=[int(a==1),int(a!=1)];u,v=1,0;out=[]
 for d in w:
  out.append(r*p*p+p*u+v)
  if d=='2':r^=1
  elif d=='0':v=(v+t[r]*u)%p;u=u*A[r]%p
  else:u=u*Ai[r]%p;v=(v-t[r]*u)%p
 assert u==1 and v==0 and r==W[k][0]
 return out+[r*p*p+p*u+v]
def ar(a):return '#['+','.join(map(str,a))+']'
S='''import RibbonOddPairTable
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
S+='def keyBank : Array (Array (Array Nat)) := #[\n'
S+=',\n'.join(ar(ar(ints(bad[i],k)) if k in used[i] else '#[]' for k in range(18))for i in range(N))+']\n'
S+='''def stored (i : Fin 28) (k : Count) : Array Nat := (keyBank[i.val]!)[k.val]!
def bankOk (i : Fin 28) (k : Count) : Prop :=
  let z := inputs i
  (stored i k).size=65 → affRow z.p z.a z.b k=stored i k
instance (i : Fin 28) (k : Count) : Decidable (bankOk i k) := by unfold bankOk; infer_instance

def fastOk (i j : Fin 28) : Prop :=
  let k := pickPair i j
  (stored i k).size=65 ∧ (stored j k).size=65 ∧
    RibbonP11Pair.checkRows (stored i k) (stored j k) (spec k)=true
instance (i j : Fin 28) : Decidable (fastOk i j) := by unfold fastOk; infer_instance
end RibbonOddFinite
'''
Path('RibbonOddPairBank.lean').write_text(S)
mods=['RibbonOddPairBank']
for a in range(0,N,4):
 nm=f'RibbonOddPairBankCheck{a//4}';mods.append(nm)
 s='''import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
 for i in range(a,min(N,a+4)):
  s+=f'theorem verifyBank{i} : ∀ k : RibbonStationaryWord.Count, bankOk {i} k := by decide +kernel\n'
  if i+1<N:s+=f'theorem verifyFast{i} : ∀ j : Fin 28, {i}<j.val → fastOk {i} j := by decide +kernel\n'
 s+='end RibbonOddFinite\n'
 Path(nm+'.lean').write_text(s)
nm='RibbonOddPairPacked';mods.append(nm)
s='\n'.join('import '+m for m in mods[1:-1])+'''
namespace RibbonOddFinite
open RibbonStationaryWord RibbonOrderThree
theorem bank_verified (i : Fin 28) (k : Count) : bankOk i k := by
  fin_cases i
'''
s+=''.join(f'  · exact verifyBank{i} k\n'for i in range(N))
s+='''theorem fast_verified (i j : Fin 28) (lt : i.val<j.val) : fastOk i j := by
  fin_cases i
'''
s+=''.join(f'  · exact verifyFast{i} j lt\n'for i in range(N-1))
s+='''  · change 27 < j.val at lt; omega

theorem pairs_checked (i j : Fin 28) (lt : i.val<j.val) : checkPair i j := by
  let k := pickPair i j
  obtain ⟨a,b,h⟩ := fast_verified i j lt
  rw [←bank_verified i k a,←bank_verified j k b] at h
  exact h

end RibbonOddFinite
#print axioms RibbonOddFinite.pairs_checked
'''
Path(nm+'.lean').write_text(s)
Path('pair_bank.order').write_text('RibbonOddPairTable '+' '.join(mods)+'\n')
print('applicable row checks',sum(map(len,used)),'of',N*18)
