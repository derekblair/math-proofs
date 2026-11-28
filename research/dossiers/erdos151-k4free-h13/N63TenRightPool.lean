import N63MaxPivotBalance
import N63TenFixedPivot
import RetentionRecipe

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

def rightPool {q : Nat} (R : Fin q → V) (y : Fin q) : Finset (Fin q) :=
  (Finset.univ.erase y).filter fun z => ¬G (R y) (R z)

theorem rightPool_card {q : Nat} (R : Fin q → V) (y : Fin q) (irr : ∀ v, ¬G v v) :
    (rightPool G R y).card = q-1-rightDeg G R y := by
  classical
  let T := (Finset.univ : Finset (Fin q)).erase y
  let A := T.filter fun z => G (R y) (R z)
  have hu : A.card = rightDeg G R y := by
    unfold rightDeg
    have hmem : y∉A := by simp [A,T]
    have he : A = Finset.univ.filter (fun z => G (R y) (R z)) := by
      ext z
      simp [A,T]
      exact fun h eq => irr _ (eq ▸ h)
    rw [he,Finset.card_eq_sum_ones,Finset.sum_filter]
  have hc : T.card = q-1 := by simp [T]
  have he : rightPool G R y = T \ A := by
    ext z
    by_cases hz : G (R y) (R z) <;> simp [rightPool,A,T,hz]
  rw [he,Finset.card_sdiff_of_subset (Finset.filter_subset _ _),hc,hu]

theorem rightPool_witness {q : Nat} (hq : q≤5) (R : Fin q → V) (y : Fin q)
    (irr : ∀ v, ¬G v v) (sym : ∀ a b, G a b ↔ G b a)
    (tf : ∀ v x y, G v x → G v y → ¬G x y) :
    ∃ S ⊆ rightPool G R y, alphaFloor (q-1-rightDeg G R y) ≤ S.card ∧
      Erdos151Ramsey.Independent (fun a b => G (R a) (R b)) S := by
  let A (a b : Fin q) := G (R a) (R b)
  letI : DecidableRel A := fun a b => inferInstanceAs (Decidable (G (R a) (R b)))
  have eq := rightPool_card G R y irr
  have e : Erdos151H13.alphaFloor (q-1-rightDeg G R y) =
      alphaFloor (q-1-rightDeg G R y) := by
    unfold Erdos151H13.alphaFloor alphaFloor
    have hh : ¬9≤q-1-rightDeg G R y := by omega
    rw [if_neg hh]
  rw [←e]
  apply Erdos151H13.choose_alpha_floor A (rightPool G R y) _
    (by omega) (fun h => (sym _ _).mp h) (fun a => irr (R a))
  intro u a b ua ab ub
  exact tf _ _ _ ua ub ab

#print axioms rightPool_witness
end Erdos151N63
