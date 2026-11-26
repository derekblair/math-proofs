from pathlib import Path
from contextlib import redirect_stdout
from io import StringIO
with redirect_stdout(StringIO()):
 exec(Path('gen_jet_bank.py').read_text())
def ord_rank(row):
 w=sorted(range(64),key=lambda i:(row[i],i))
 v=[None]*64
 for j,k in enumerate(w):v[k]=j
 assert all(w[v[k]]==k for k in range(64))
 return ar(v),ar(w)
S='''import RibbonOddJetBank
import RibbonOddRowSort
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord RibbonOddRowSort
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
for i in range(N):
 S+=f'def permRow{i} : Array Sorting := '+ar('⟨'+','.join(ord_rank(ints(bad[i],d,k)))+'⟩' for d,k in P[i])+'\n'
S+='def permBank : Array (Array Sorting) := '+ar('permRow'+str(i)for i in range(N))+'\n'
S+='''instance : Inhabited Sorting := ⟨⟨#[],#[]⟩⟩

def sorting (i : Fin 28) (d : Dir i) : Sorting := (permBank[i.val]!)[d.val]!
def sortedOk (i : Fin 28) (d : Dir i) : Prop :=
  let k := pickJet i d
  Valid (storedJet i d) (storedJet i d) (spec k) (sorting i d)
instance (i : Fin 28) (d : Dir i) : Decidable (sortedOk i d) := by unfold sortedOk; infer_instance
end RibbonOddFinite
'''
Path('RibbonOddJetSortData.lean').write_text(S)
mods=['RibbonOddJetTable','RibbonOddJetBank','RibbonOddJetSortData']
for a in range(0,N,4):
 nm=f'RibbonOddJetSortCheck{a//4}';mods.append(nm)
 s='''import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
 for i in range(a,min(N,a+4)):
  s+=f'theorem verifyJetBank{i} : ∀ d : Dir {i}, jetBankOk {i} d := by decide +kernel\n'
  s+=f'theorem verifyJetSort{i} : ∀ d : Dir {i}, sortedOk {i} d := by decide +kernel\n'
 s+='end RibbonOddFinite\n';Path(nm+'.lean').write_text(s)
nm='RibbonOddJetSorted';s='\n'.join('import '+m for m in mods[3:])+'''
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord RibbonOddRowSort
theorem jet_bank_verified (i : Fin 28) (d : Dir i) : jetBankOk i d := by
  fin_cases i
'''
s+=''.join(f'  · exact verifyJetBank{i} d\n'for i in range(N))
s+='''theorem jet_sort_verified (i : Fin 28) (d : Dir i) : sortedOk i d := by
  fin_cases i
'''
s+=''.join(f'  · exact verifyJetSort{i} d\n'for i in range(N))
s+='''theorem jet_sorted_sound (i : Fin 28) (d : Dir i) (p q : Fin 64)
    (lt : p.val<q.val)
    (eq : jetPoint i (direction i d).1 (direction i d).2 (pickJet i d) p =
      jetPoint i (direction i d).1 (direction i d).2 (pickJet i d) q) :
    IsMate (spec (pickJet i d)) p.val q.val := by
  have H := jet_sort_verified i d
  have E := jet_bank_verified i d
  unfold jetBankOk at E
  have same : (storedJet i d)[p.val]! = (storedJet i d)[q.val]! := by
    rw [←E,jet_at,jet_at,congrArg (jetKey i) eq]
  exact checked H p q lt same same

end RibbonOddFinite
#print axioms RibbonOddFinite.jet_sorted_sound
'''
Path(nm+'.lean').write_text(s)
Path('jet_sort.order').write_text(' '.join(mods+[nm])+'\n')
