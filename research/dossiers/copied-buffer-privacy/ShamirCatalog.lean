import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

open Polynomial
open scoped BigOperators

namespace ShamirCatalog

variable {F : Type*} [Field F]

noncomputable def vanish (S : Finset F) : F[X] :=
  ∏ a ∈ S, (1 - C a⁻¹ * X)

theorem vanish_const (S : Finset F) : (vanish S).eval 0 = 1 := by
  simp [vanish, Polynomial.eval_prod]

theorem vanish_degree (S : Finset F) : (vanish S).natDegree ≤ S.card := by
  calc
    _ ≤ ∑ a ∈ S, (1 - C a⁻¹ * X : F[X]).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _a ∈ S, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro a _
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      simpa using Polynomial.natDegree_C_mul_X_pow_le (a⁻¹) 1
    _ = _ := by simp

theorem vanish_site (S : Finset F) (nonzero : ∀ a ∈ S, a ≠ 0)
    {a : F} (ha : a ∈ S) : (vanish S).eval a = 0 := by
  rw [vanish, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  exact ⟨a,ha,by simp [inv_mul_cancel₀ (nonzero a ha)]⟩

/-- Fixed views represented once per distinct origin site. -/
def Fibre (S : Finset F) (t : ℕ) (s : F) (v : F → F) :=
  { f : F[X] // f.natDegree ≤ t ∧ f.eval 0 = s ∧ ∀ x ∈ S, f.eval x = v x }

noncomputable def translateFibre (S : Finset F) (t : ℕ) (s s' : F)
    (v : F → F) (nonzero : ∀ x ∈ S, x ≠ 0) (small : S.card ≤ t) :
    Fibre S t s v ≃ Fibre S t s' v := by
  let d := C (s'-s) * vanish S
  have deg : d.natDegree ≤ t := by
    calc
      _ ≤ (C (s'-s)).natDegree + (vanish S).natDegree := natDegree_mul_le
      _ = (vanish S).natDegree := by simp
      _ ≤ _ := (vanish_degree S).trans small
  have atZero : d.eval 0 = s'-s := by simp [d, vanish_const]
  have atSite (x) (hx : x ∈ S) : d.eval x = 0 := by simp [d,vanish_site S nonzero hx]
  refine {
    toFun := fun f => ⟨f.1+d, ?_⟩
    invFun := fun f => ⟨f.1-d, ?_⟩
    left_inv := fun f => Subtype.ext (add_sub_cancel_right _ _)
    right_inv := fun f => Subtype.ext (sub_add_cancel _ _)
  }
  · refine ⟨(natDegree_add_le _ _).trans (max_le_max f.2.1 deg |>.trans (by simp)),?_,?_⟩
    · simp only [eval_add,f.2.2.1,atZero]; ring
    · intro x hx
      simp [atSite x hx,f.2.2.2 x hx]
  · refine ⟨(natDegree_sub_le _ _).trans (max_le_max f.2.1 deg |>.trans (by simp)),?_,?_⟩
    · simp only [eval_sub,f.2.2.1,atZero]; ring
    · intro x hx
      simp [atSite x hx,f.2.2.2 x hx]

theorem reconstruct_const (S : Finset F) (t : ℕ) (large : t < S.card)
    (p q : F[X]) (dp : p.natDegree ≤ t) (dq : q.natDegree ≤ t)
    (same : ∀ a ∈ S, p.eval a=q.eval a) : p=q := by
  by_contra ne
  have roots : S.card ≤ (p-q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    apply (Polynomial.mem_roots (sub_ne_zero.mpr ne)).2
    simp [same a ha]
  exact (not_le_of_gt large) (roots.trans ((natDegree_sub_le _ _).trans (max_le dp dq)))

/-- Two different secrets have disjoint transcript supports above threshold. -/
theorem distinctSecretsDisjoint (S : Finset F) (t : ℕ) (large : t < S.card)
    (s s' : F) (diff : s ≠ s') (v : F → F)
    (p : Fibre S t s v) (q : Fibre S t s' v) : False := by
  have e := reconstruct_const S t large p.1 q.1 p.2.1 q.2.1
    (fun a h => (p.2.2.2 a h).trans (q.2.2.2 a h).symm)
  exact diff (p.2.2.1.symm.trans ((congrArg (Polynomial.eval 0) e).trans q.2.2.1))

/-- Combining origins is a product at the level of transcript fibres.
Jointly independent uniform coefficient vectors produce the corresponding
product measure over finite fields. The probability model is not encoded here. -/
noncomputable def translateOrigins {J : Type*} (S : J → Finset F)
    (t : ℕ) (s s' : F) (v : J → F → F)
    (nonzero : ∀ j a, a ∈ S j → a ≠ 0) (small : ∀ j, (S j).card ≤ t) :
    (∀ j, Fibre (S j) t s (v j)) ≃ (∀ j, Fibre (S j) t s' (v j)) :=
  Equiv.piCongrRight (fun j => translateFibre (S j) t s s' (v j) (nonzero j) (small j))

theorem oneOriginSeparates {J : Type*} (S : J → Finset F) (t : ℕ)
    (s s' : F) (v : J → F → F) (diff : s ≠ s') (j : J) (large : t < (S j).card)
    (p : ∀ j, Fibre (S j) t s (v j)) (q : ∀ j, Fibre (S j) t s' (v j)) : False :=
  distinctSecretsDisjoint (S j) t large s s' diff (v j) (p j) (q j)

#print axioms translateOrigins
#print axioms oneOriginSeparates
#print axioms translateFibre
#print axioms reconstruct_const
#print axioms distinctSecretsDisjoint
end ShamirCatalog
