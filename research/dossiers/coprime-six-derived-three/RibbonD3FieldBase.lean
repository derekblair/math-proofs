import RibbonD3FieldBaseData

namespace RibbonD3Field
open RibbonAffine (eRow)
variable {K : Type*} [Field K]

def rowCheck (i : Nat) : Bool :=
  (List.range baseChart.reps.size).all fun j =>
    if i<j then decide (pairValid branch baseChart.reps[i]! baseChart.reps[j]! (pick i j)) else true

def chunkCheck (h : Fin 16) : Bool :=
  (List.range 8).all fun i => if 8*h.val+i<baseChart.reps.size then rowCheck (8*h.val+i) else true

set_option maxRecDepth 30000
set_option maxHeartbeats 0
private theorem checks (h : Fin 16) : chunkCheck h=true := by fin_cases h <;> decide +kernel

private theorem base_valid (i j : Fin baseChart.reps.size) (lt : i.val<j.val) :
    pairValid branch baseChart.reps[i] baseChart.reps[j] (pick i.val j.val) := by
  have hi := i.isLt
  have hj := j.isLt
  have size : baseChart.reps.size≤128 := by decide +kernel
  have H : i.val/8<16 := by omega
  let b : Fin 16 := ⟨i.val/8,H⟩
  have r := checks b
  have e : 8*b.val+i.val%8=i.val := by dsimp [b]; omega
  have m := List.all_eq_true.mp r (i.val%8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have R : rowCheck i.val=true := by simpa only [e,hi,ite_true] using m
  have B := List.all_eq_true.mp R j.val (List.mem_range.mpr hj)
  have S := of_decide_eq_true (by simpa only [lt,ite_true] using B :
    decide (pairValid branch baseChart.reps[i.val]! baseChart.reps[j.val]! (pick i.val j.val))=true)
  simpa only [Fin.getElem_fin,getElem!_pos baseChart.reps i.val hi,getElem!_pos baseChart.reps j.val hj] using S

theorem base_cases (a b : Kˣ) (n : Nat) (aN : a^n=1) (bN : b^n=1) (a1 : a≠1)
    (odd : Odd n) (no3 : ¬3∣n) (two : (2:K)≠0) (three : (3:K)≠0) :
    Ordered baseChart a b ∨ BaseFault branch a b n := by
  classical
  by_cases S : Ordered baseChart a b
  · exact Or.inl S
  · unfold Ordered at S
    push_neg at S
    obtain ⟨i,j,l,eq⟩ := S
    exact Or.inr (base_failure branch _ _ _ (base_valid i j l) a b n aN bN a1 odd no3 two three eq)

end RibbonD3Field
#print axioms RibbonD3Field.base_cases
