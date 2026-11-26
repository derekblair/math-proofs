from ast import literal_eval
from pathlib import Path
P=literal_eval(next(l.split(': ',1)[1]for l in Path('projected_three_main.log').read_text().splitlines() if l.startswith('main table projected + single:')))
assert len(P)==28 and all(k in (0,2,3) for k in P.values())
S='''import RibbonOrderThreeAff
namespace RibbonOrderThree
open RibbonStationaryWord
set_option maxRecDepth 32000
set_option maxHeartbeats 0
structure Input where
  p : Nat
  a : Nat
  b : Nat
  word : W3
'''
S+='def inputs : Fin 28 → Input := !['+','.join('⟨'+','.join(map(str,(*tr,(0,2,3).index(k))))+'⟩' for tr,k in P.items())+']\n'
S+='''def Ok (i : Fin 28) : Prop :=
  let z := inputs i
  RibbonP11Pair.checkRows (lowRow z.word) (affRow z.p z.a z.b (wid z.word)) (spec (wid z.word))=true
instance (i : Fin 28) : Decidable (Ok i) := by unfold Ok; infer_instance
'''
for i in range(28): S+=f'private theorem input{i} : Ok {i} := by decide +kernel\n'
S+='\ntheorem all_inputs (i : Fin 28) : Ok i := by\n  fin_cases i\n'
for i in range(28):S+=f'  · exact input{i}\n'
S+='\nend RibbonOrderThree\n#print axioms RibbonOrderThree.all_inputs\n'
Path('RibbonOrderThreeCert.lean').write_text(S)
