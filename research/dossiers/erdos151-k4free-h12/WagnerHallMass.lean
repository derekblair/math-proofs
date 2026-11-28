import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

open scoped BigOperators
namespace Erdős151.H12.Wagner

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def mass (A : L → R → Prop) [DecidableRel A] (S : Finset L) (T : Finset R) : ℕ :=
  ∑ s ∈ S, ∑ t ∈ T, if A s t then 1 else 0

theorem transpose (A : L → R → Prop) [DecidableRel A] (S : Finset L) (T : Finset R) :
    mass A S T = ∑ t ∈ T, ∑ s ∈ S, if A s t then (1:ℕ) else 0 :=
  Finset.sum_comm

theorem split_right (A : L → R → Prop) [DecidableRel A] (S : Finset L)
    (T U : Finset R) (dis : Disjoint T U) :
    mass A S (T∪U) = mass A S T + mass A S U := by
  simp only [mass,Finset.sum_union dis,Finset.sum_add_distrib]

theorem split_left (A : L → R → Prop) [DecidableRel A] (S P : Finset L)
    (T : Finset R) (dis : Disjoint S P) :
    mass A (S∪P) T = mass A S T + mass A P T := by
  simp only [mass,Finset.sum_union dis]

theorem mass_zero (A : L → R → Prop) [DecidableRel A] (S : Finset L) (T : Finset R)
    (h : ∀ s ∈ S, ∀ t ∈ T, ¬A s t) : mass A S T = 0 := by
  unfold mass
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro t ht
  simp [h s hs t ht]

theorem mass_le_card_left (A : L → R → Prop) [DecidableRel A]
    (S : Finset L) (T : Finset R)
    (one : ∀ s ∈ S, ∀ t ∈ T, ∀ u ∈ T, A s t → A s u → t=u) :
    mass A S T ≤ S.card := by
  unfold mass
  calc
    _ ≤ ∑ _s ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro s hs
      have hcard : (T.filter (A s)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro t ht u hu
        exact one s hs t (Finset.mem_filter.mp ht).1 u (Finset.mem_filter.mp hu).1
          (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp hu).2
      rw [← Finset.sum_filter]
      simpa using hcard
    _ = _ := by simp

theorem mass_le_card_right (A : L → R → Prop) [DecidableRel A]
    (S : Finset L) (T : Finset R)
    (one : ∀ t ∈ T, ∀ s ∈ S, ∀ u ∈ S, A s t → A u t → s=u) :
    mass A S T ≤ T.card := by
  rw [transpose]
  exact mass_le_card_left (fun t s => A s t) T S one

theorem add_complement (S : Finset L) :
    S ∪ (Finset.univ \ S) = Finset.univ := by
  ext x
  by_cases h : x∈S <;> simp [h]

theorem dis_complement (S : Finset L) : Disjoint S (Finset.univ \ S) :=
  Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)

def cutMass (A : L → R → Prop) [DecidableRel A] (S : Finset L) (T : Finset R) : ℕ :=
  mass A S (Finset.univ \ T) + mass A (Finset.univ \ S) T

/-- Counting form of the Hall-deficient side; no graph cycle formalism. -/
theorem hall_deficit_mass (A : L → R → Prop) [DecidableRel A]
    (row : ∀ s, (∑ t : R, if A s t then (1:ℕ) else 0) = 3)
    (col : ∀ t, (∑ s : L, if A s t then (1:ℕ) else 0) = 3)
    (S : Finset L) (T B : Finset R)
    (dis : Disjoint T B) (hdef : T.card < S.card)
    (dead : ∀ s ∈ S, ∀ t, t∉T → t∉B → ¬ A s t)
    (h4 : mass A S B ≤ 4) (hS : mass A S B ≤ S.card) :
    3 ≤ S.card ∧ cutMass A S T ≤ 5 ∧ S.card + T.card ≤ mass A S T := by
  have hsub : B ⊆ Finset.univ \ T := fun b hb =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun ht => Finset.disjoint_left.mp dis ht hb⟩
  let U := (Finset.univ \ T) \ B
  have he : B ∪ U = Finset.univ \ T := by
    ext x
    by_cases hx : x∈B
    · simp [U,hx,hsub hx]
    · simp [U,hx]
  have hu : mass A S U = 0 := by
    apply mass_zero
    intro s hs t ht
    have h0 := Finset.mem_sdiff.mp ht
    exact dead s hs t (Finset.mem_sdiff.mp h0.1).2 h0.2
  have hdis : Disjoint B U := Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  have hsplt : mass A S (Finset.univ \ T) = mass A S B := by
    rw [← he,split_right A S B U hdis,hu,add_zero]
  have mr : mass A S Finset.univ = 3*S.card := by
    simp [mass,row,Nat.mul_comm]
  have mc : mass A Finset.univ T = 3*T.card := by
    rw [transpose]; simp [col,Nat.mul_comm]
  have hr := split_right A S T (Finset.univ \ T) (dis_complement T)
  rw [add_complement,mr,hsplt] at hr
  have hc := split_left A S (Finset.univ \ S) T (dis_complement S)
  rw [add_complement,mc] at hc
  unfold cutMass
  rw [hsplt]
  omega

#print axioms mass_le_card_left
#print axioms mass_le_card_right
#print axioms hall_deficit_mass
end Erdős151.H12.Wagner
