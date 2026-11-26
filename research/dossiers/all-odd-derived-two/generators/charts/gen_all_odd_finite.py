from pathlib import Path
from itertools import combinations
from contextlib import redirect_stdout
from io import StringIO
with redirect_stdout(StringIO()):
 exec(Path('reconnaissance_actual.py').read_text())
N=len(bad)
P={ (i,j):next(k for k,R in enumerate(tab) if not (R[i]&R[j])) for i,j in combinations(range(N),2)}
s='''import RibbonOrderThreeCert
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
s+='def pickPair : Fin 28 → Fin 28 → Count := !['+','.join('!['+','.join(str(P.get((i,j),0)) for j in range(N))+']'for i in range(N))+']\n'
s+='''def checkPair (i j : Fin 28) : Prop :=
  let a := inputs i
  let b := inputs j
  let k := pickPair i j
  RibbonP11Pair.checkRows (affRow a.p a.a a.b k) (affRow b.p b.a b.b k) (spec k)=true
instance (i j : Fin 28) : Decidable (checkPair i j) := by unfold checkPair; infer_instance
'''
for i in range(N-1):
 s+=f'private theorem check{i} : ∀ j : Fin 28, {i}<j.val → checkPair {i} j := by decide +kernel\n'
s+='\ntheorem pairs_checked (i j : Fin 28) (lt : i.val<j.val) : checkPair i j := by\n  fin_cases i\n'
for i in range(N-1):s+=f'  · exact check{i} j lt\n'
s+='  · change 27 < j.val at lt; omega\n\nend RibbonOddFinite\n#print axioms RibbonOddFinite.pairs_checked\n'
Path('RibbonOddPairCert.lean').write_text(s)

P={tuple(i):[next(k for k,w in enumerate(W) if not collision(w,*i,*dd))for dd in [(0,1)]+[(1,q)for q in range(i[0])]]for i in bad}
s='''import RibbonOddJetCore
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord
set_option maxHeartbeats 0
set_option maxRecDepth 30000
'''
s+='def jetTable : Array (Array Count) := #['+','.join('#['+','.join(map(str,r))+']' for r in P.values())+']\n'
s+='''def pickJet (i : Fin 28) (d : Dir i) : Count := (jetTable[i.val]!)[d.val]!
def checkJet (i : Fin 28) (d : Dir i) : Prop :=
  let k := pickJet i d
  let row := jetRow i (direction i d).1 (direction i d).2 k
  RibbonP11Pair.checkRows row row (spec k)=true
instance (i : Fin 28) (d : Dir i) : Decidable (checkJet i d) := by unfold checkJet; infer_instance
'''
for i in range(N):
 s+=f'private theorem checkj{i} : ∀ d : Dir {i}, checkJet {i} d := by decide +kernel\n'
s+='\ntheorem jets_checked (i : Fin 28) (d : Dir i) : checkJet i d := by\n  fin_cases i\n'
for i in range(N):s+=f'  · exact checkj{i} d\n'
s+='\nend RibbonOddFinite\n#print axioms RibbonOddFinite.jets_checked\n'
Path('RibbonOddJetCert.lean').write_text(s)
print(len(P),sum(map(len,P.values())))
