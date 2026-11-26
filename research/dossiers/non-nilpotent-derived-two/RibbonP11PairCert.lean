import RibbonP11PairPacked
namespace RibbonP11Pair
open RibbonStationaryWord
set_option maxRecDepth 32000
set_option maxHeartbeats 0
def pick : Fin 16 → Fin 16 → Count := ![![0,6,0,7,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,2],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
def ok (i j : Fin 16) : Prop :=
  checkRows (row (bad i) (pick i j)) (row (bad j) (pick i j)) (spec (pick i j))=true
instance (i j : Fin 16) : Decidable (ok i j) := by unfold ok; infer_instance
private theorem ok0 : ∀ j : Fin 16, 0<j.val → ok 0 j := by decide +kernel
private theorem ok1 : ∀ j : Fin 16, 1<j.val → ok 1 j := by decide +kernel
private theorem ok2 : ∀ j : Fin 16, 2<j.val → ok 2 j := by decide +kernel
private theorem ok3 : ∀ j : Fin 16, 3<j.val → ok 3 j := by decide +kernel
private theorem ok4 : ∀ j : Fin 16, 4<j.val → ok 4 j := by decide +kernel
private theorem ok5 : ∀ j : Fin 16, 5<j.val → ok 5 j := by decide +kernel
private theorem ok6 : ∀ j : Fin 16, 6<j.val → ok 6 j := by decide +kernel
private theorem ok7 : ∀ j : Fin 16, 7<j.val → ok 7 j := by decide +kernel
private theorem ok8 : ∀ j : Fin 16, 8<j.val → ok 8 j := by decide +kernel
private theorem ok9 : ∀ j : Fin 16, 9<j.val → ok 9 j := by decide +kernel
private theorem ok10 : ∀ j : Fin 16, 10<j.val → ok 10 j := by decide +kernel
private theorem ok11 : ∀ j : Fin 16, 11<j.val → ok 11 j := by decide +kernel
private theorem ok12 : ∀ j : Fin 16, 12<j.val → ok 12 j := by decide +kernel
private theorem ok13 : ∀ j : Fin 16, 13<j.val → ok 13 j := by decide +kernel
private theorem ok14 : ∀ j : Fin 16, 14<j.val → ok 14 j := by decide +kernel

theorem certified (i j : Fin 16) (lt : i.val<j.val) : property (pick i j) (bad i) (bad j) := by
  apply rows_sound
  fin_cases i
  · exact ok0 j lt
  · exact ok1 j lt
  · exact ok2 j lt
  · exact ok3 j lt
  · exact ok4 j lt
  · exact ok5 j lt
  · exact ok6 j lt
  · exact ok7 j lt
  · exact ok8 j lt
  · exact ok9 j lt
  · exact ok10 j lt
  · exact ok11 j lt
  · exact ok12 j lt
  · exact ok13 j lt
  · exact ok14 j lt
  · change 15 < j.val at lt; omega

end RibbonP11Pair
#print axioms RibbonP11Pair.certified
