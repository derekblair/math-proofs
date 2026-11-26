import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace QuorumMinimum

def zeros {n : Nat} (p : Fin n → Bool) : Nat :=
  ∑ i, if p i then 0 else 1

def bitWeight (b : Bool) : Nat := if b then 1 else 2

theorem weightSum (n : Nat) : (∑ p : Fin n → Bool, 2^zeros p) = 3^n := by
  have h : (∑ b : Bool, bitWeight b) = 3 := by decide
  rw [← h, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p _
  unfold zeros
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> simp [bitWeight]

noncomputable def bad (r : Nat) : Finset (Fin (8*r) → Bool) :=
  Finset.univ.filter (fun p => 6*r ≤ zeros p)

/-- With 8r independent bits, at most 2^(7r) assignments have ≥6r zeros. -/
theorem bad_card (r : Nat) : (bad r).card ≤ 2^(7*r) := by
  classical
  have A : (bad r).card * 2^(6*r) ≤ ∑ p ∈ bad r, 2^zeros p := by
    calc
      (bad r).card * 2^(6*r) = ∑ _p ∈ bad r, 2^(6*r) := by simp [Nat.mul_comm]
      _ ≤ ∑ p ∈ bad r, 2^zeros p := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : 6*r ≤ zeros p := (Finset.mem_filter.mp hp).2
        exact Nat.pow_le_pow_right (by decide) hp'
  have B : (∑ p ∈ bad r, 2^zeros p) ≤ (∑ p : Fin (8*r) → Bool, 2^zeros p) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intros
    exact Nat.zero_le _
  have C : 3^(8*r) ≤ (2:Nat)^(13*r) := by
    simp only [pow_mul]
    exact Nat.pow_le_pow_left (by decide : (3:Nat)^8 ≤ 2^13) r
  have D := le_trans A (le_trans B ((weightSum (8*r)).le.trans C))
  have sum : 13*r = 7*r+6*r := by omega
  rw [sum,pow_add] at D
  exact Nat.le_of_mul_le_mul_right D (Nat.pow_pos (by decide))

/-- Alternate XHigh cross-check: use 3 per zero and 1 per one. -/
theorem weightSumThree (n : Nat) : (∑ p : Fin n → Bool, 3^zeros p) = 4^n := by
  let w (b : Bool) : Nat := if b then 1 else 3
  have h : (∑ b : Bool, w b) = 4 := by decide
  rw [← h, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p _
  unfold zeros
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> simp [w]

theorem bad_card_three (r : Nat) : (bad r).card ≤ 2^(7*r) := by
  classical
  have A : (bad r).card * 2^(9*r) ≤ ∑ p ∈ bad r, 3^zeros p := by
    calc
      (bad r).card * 2^(9*r) = ∑ _p ∈ bad r, 2^(9*r) := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have X : (2:Nat)^(9*r) ≤ 3^(6*r) := by
          rw [pow_mul,pow_mul]
          exact Nat.pow_le_pow_left (by decide : (2:Nat)^9 ≤ 3^6) r
        exact X.trans (Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp hp).2)
  have B : (∑ p ∈ bad r, 3^zeros p) ≤ (∑ p : Fin (8*r) → Bool, 3^zeros p) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have D := A.trans (B.trans (weightSumThree (8*r)).le)
  have fact : (4:Nat)^(8*r) = 2^(7*r)*2^(9*r) := by
    rw [←pow_add,pow_mul]
    have h : 7*r+9*r=16*r := by omega
    rw [h,pow_mul]
    have hbase : (4:Nat)^8=2^16 := by decide
    rw [hbase]
  rw [fact] at D
  exact Nat.le_of_mul_le_mul_right D (Nat.pow_pos (by decide))

#print axioms bad_card_three

theorem pullback_card {Ω P R : Type} [Fintype Ω] [Fintype R]
    [DecidableEq P] (e : Ω ≃ P × R) (B : Finset P) :
    (Finset.univ.filter (fun w => (e w).1 ∈ B)).card = B.card * Fintype.card R := by
  classical
  have eq : Finset.univ.filter (fun w => (e w).1 ∈ B) =
      (B ×ˢ (Finset.univ : Finset R)).map e.symm.toEmbedding := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply, Finset.mem_product]
    constructor
    · intro hw
      exact ⟨e w, ⟨hw, trivial⟩, e.symm_apply_apply w⟩
    · rintro ⟨x,hx,hxw⟩
      simpa [← hxw] using hx.1
  rw [eq, Finset.card_map, Finset.card_product, Finset.card_univ]

theorem exists_outside_family {Ω I : Type} [Fintype Ω] [Fintype I]
    (badCase : I → Finset Ω) (cap : Nat)
    (hcap : ∀ i, (badCase i).card ≤ cap)
    (strict : Fintype.card I * cap < Fintype.card Ω) :
    ∃ w : Ω, ∀ i, w ∉ badCase i := by
  classical
  let U : Finset Ω := (Finset.univ : Finset I).biUnion badCase
  have ub : U.card ≤ Fintype.card I * cap := by
    calc
      U.card ≤ ∑ i : I, (badCase i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : I, cap := Finset.sum_le_sum fun i _ => hcap i
      _ = _ := by simp [Nat.mul_comm]
  have proper : U ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, fun eq => by rw [eq,Finset.card_univ] at ub; omega⟩
  obtain ⟨w, -, hw⟩ := Finset.exists_of_ssubset proper
  exact ⟨w, fun i hi => hw (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)⟩

#print axioms pullback_card
#print axioms exists_outside_family
#print axioms weightSum
#print axioms bad_card

end QuorumMinimum
