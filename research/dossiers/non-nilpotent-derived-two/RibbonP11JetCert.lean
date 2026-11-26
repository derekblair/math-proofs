import RibbonP11JetCalc
namespace RibbonP11JetCalc
open RibbonP11Pair RibbonStationaryWord
set_option maxRecDepth 32000
set_option maxHeartbeats 0

def direction : Fin 12 → F × F := ![(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),
  (1,5),(1,6),(1,7),(1,8),(1,9),(1,10)]
def jetPick : Fin 16 → Fin 12 → Count := ![![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,2,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,2,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,2,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,2,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,2]]
def ok (i : Fin 16) (d : Fin 12) : Prop :=
  let k := jetPick i d
  let r := jetRow i (direction d).1 (direction d).2 k
  checkRows r r (spec k)=true
instance (i : Fin 16) (d : Fin 12) : Decidable (ok i d) := by unfold ok; infer_instance
private theorem pilot0 : ∀ d : Fin 12, ok 0 d := by decide +kernel
private theorem pilot1 : ∀ d : Fin 12, ok 1 d := by decide +kernel
private theorem pilot2 : ∀ d : Fin 12, ok 2 d := by decide +kernel
private theorem pilot3 : ∀ d : Fin 12, ok 3 d := by decide +kernel
private theorem pilot4 : ∀ d : Fin 12, ok 4 d := by decide +kernel
private theorem pilot5 : ∀ d : Fin 12, ok 5 d := by decide +kernel
private theorem pilot6 : ∀ d : Fin 12, ok 6 d := by decide +kernel
private theorem pilot7 : ∀ d : Fin 12, ok 7 d := by decide +kernel
private theorem pilot8 : ∀ d : Fin 12, ok 8 d := by decide +kernel
private theorem pilot9 : ∀ d : Fin 12, ok 9 d := by decide +kernel
private theorem pilot10 : ∀ d : Fin 12, ok 10 d := by decide +kernel
private theorem pilot11 : ∀ d : Fin 12, ok 11 d := by decide +kernel
private theorem pilot12 : ∀ d : Fin 12, ok 12 d := by decide +kernel
private theorem pilot13 : ∀ d : Fin 12, ok 13 d := by decide +kernel
private theorem pilot14 : ∀ d : Fin 12, ok 14 d := by decide +kernel
private theorem pilot15 : ∀ d : Fin 12, ok 15 d := by decide +kernel

theorem certified (i : Fin 16) (d : Fin 12) (p q : Fin 64) (lt : p.val<q.val)
    (e : jetPoint i (direction d).1 (direction d).2 (jetPick i d) p=
      jetPoint i (direction d).1 (direction d).2 (jetPick i d) q) :
    IsMate (spec (jetPick i d)) p.val q.val := by
  apply row_sound _ p q lt e
  change ok i d
  fin_cases i
  · exact pilot0 d
  · exact pilot1 d
  · exact pilot2 d
  · exact pilot3 d
  · exact pilot4 d
  · exact pilot5 d
  · exact pilot6 d
  · exact pilot7 d
  · exact pilot8 d
  · exact pilot9 d
  · exact pilot10 d
  · exact pilot11 d
  · exact pilot12 d
  · exact pilot13 d
  · exact pilot14 d
  · exact pilot15 d

end RibbonP11JetCalc
#print axioms RibbonP11JetCalc.certified
