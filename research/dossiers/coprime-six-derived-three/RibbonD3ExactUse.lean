import RibbonD3RBinding
import RibbonD3ExactCheck

namespace RibbonD3MateUse
open RibbonD3MateData RibbonD3SignedEval RibbonD3Grid RibbonD3PortEval RibbonDerived3
variable {G : Type*} [Group G]

def exactReference (C : Chart) (r : ExactRow) :=
  r.conjugator ++ (if r.sign == 1 then letters C r.baseLength
    else inverse (letters C r.baseLength)) ++ inverse r.conjugator

theorem checkExact_true (i : Fin charts.size) (j : Fin (exactRows[i.val]!).size) :
    checkExact charts[i.val]! (exactRows[i.val]!)[j] = true := by
  have q := List.all_eq_true.mp checkExactAll_true i.val (by simp [i.isLt])
  exact Array.all_eq_true.mp q j.val j.isLt

theorem exact_information (i : Fin charts.size) (j : Fin (exactRows[i.val]!).size) :
    let C := charts[i.val]!
    let r := (exactRows[i.val]!)[j]
    (r.baseLength = 32 ∨ r.baseLength = 64) ∧ (r.sign = 1 ∨ r.sign = -1) ∧
    r.baseLength ≤ r.j ∧ (r.baseLength = 32 → r.j < 64) ∧
    freeReduce (ratio C r.i r.j) = freeReduce (exactReference C r) := by
  dsimp
  have h := checkExact_true i j
  change ((((exactRows[i.val]!)[j].baseLength == 32 ||
      (exactRows[i.val]!)[j].baseLength == 64) &&
    ((exactRows[i.val]!)[j].sign == 1 || (exactRows[i.val]!)[j].sign == -1) &&
    (decide ((exactRows[i.val]!)[j].baseLength ≤ (exactRows[i.val]!)[j].j)) &&
    (if (exactRows[i.val]!)[j].baseLength == 32 then decide ((exactRows[i.val]!)[j].j < 64)
      else (exactRows[i.val]!)[j].j-(exactRows[i.val]!)[j].i == 64) &&
    freeReduce (ratio charts[i.val]! (exactRows[i.val]!)[j].i (exactRows[i.val]!)[j].j) ==
      freeReduce (exactReference charts[i.val]! (exactRows[i.val]!)[j])) = true) at h
  simp only [Bool.and_eq_true_iff,Bool.or_eq_true_iff,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨H,S⟩,L⟩,M⟩,Z⟩ := h
  exact ⟨H,S,L,fun b => by simpa [b] using M,Z⟩

theorem exact_mate_eval (x y : G) (i : Fin charts.size) (j : Fin (exactRows[i.val]!).size) :
    let C := charts[i.val]!
    let r := (exactRows[i.val]!)[j]
    eval (letter x y) (ratio C r.i r.j) =
      eval (letter x y) (exactReference C r) :=
  free_sound x y (exact_information i j).2.2.2.2

#print axioms exact_mate_eval
end RibbonD3MateUse
