import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace WagnerMinority
open scoped BigOperators

variable {V : Type*} [DecidableEq V]
set_option linter.unusedSectionVars false

/-- A host set of at most three vertices contains at most three graph edges. -/
theorem edge_card_small (U : Finset V) (S : Finset (Finset V))
    (hU : U.card ≤ 3) (hS : ∀ e ∈ S, e ⊆ U ∧ e.card = 2) :
    S.card ≤ 3 := by
  have H : S ⊆ U.powersetCard 2 := fun e he =>
    Finset.mem_powersetCard.mpr (hS e he)
  calc
    S.card ≤ (U.powersetCard 2).card := Finset.card_le_card H
    _ = U.card.choose 2 := Finset.card_powersetCard _ _
    _ ≤ (3 : ℕ).choose 2 := Nat.choose_le_choose _ hU
    _ = 3 := by decide

/-- Two distinct actual graph edges in the minority side uniquely determine
their incident triangle, namely the three-vertex mixed host set. -/
theorem rich_triangle (U e f t : Finset V)
    (hU : U.card ≤ 3) (heU : e ⊆ U) (hfU : f ⊆ U)
    (he : e.card = 2) (hf : f.card = 2)
    (ht : t.card = 3) (hne : e ≠ f) (het : e ⊆ t) (hft : f ⊆ t) :
    t = U := by
  have hEU : e ⊆ e ∪ f := Finset.subset_union_left
  have hFU : f ⊆ e ∪ f := Finset.subset_union_right
  have hUe : 2 < (e ∪ f).card := by
    by_contra! H
    have eqe : e = e ∪ f := Finset.eq_of_subset_of_card_le hEU (by omega)
    have eqf : f = e ∪ f := Finset.eq_of_subset_of_card_le hFU (by omega)
    exact hne (eqe.trans eqf.symm)
  have hvU : e ∪ f = U := Finset.eq_of_subset_of_card_le
    (Finset.union_subset heU hfU) (by omega)
  have hvt : e ∪ f = t := Finset.eq_of_subset_of_card_le
    (Finset.union_subset het hft) (by omega)
  exact hvt.symm.trans hvU

/-- At most one triangle has two or more of these minority edges; that one
triangle contributes at most two extra incidences above one per triangle. -/
theorem minority_incidence (U : Finset V) (S T : Finset (Finset V))
    (hU : U.card ≤ 3) (hS : ∀ e ∈ S, e ⊆ U ∧ e.card = 2)
    (hT : ∀ t ∈ T, t.card = 3) :
    (∑ t ∈ T, (S.filter (· ⊆ t)).card) ≤ T.card + 2 := by
  have hc := edge_card_small U S hU hS
  have hp : ∀ t ∈ T, (S.filter (· ⊆ t)).card ≤
      1 + (if t = U then 2 else 0) := by
    intro t ht
    by_cases heq : t = U
    · rw [ite_eq_left heq]
      exact (Finset.card_filter_le _ _).trans hc
    · rw [ite_eq_right heq]
      by_contra! hn
      obtain ⟨e, f, he, hf, hd⟩ := Finset.one_lt_card_iff.mp (by simpa using hn)
      have hEs := Finset.mem_filter.mp he
      have hFs := Finset.mem_filter.mp hf
      exact heq (rich_triangle U e f t hU (hS e hEs.1).1 (hS f hFs.1).1
        (hS e hEs.1).2 (hS f hFs.1).2 (hT t ht) hd hEs.2 hFs.2)
  calc
    (∑ t ∈ T, (S.filter (· ⊆ t)).card) ≤ ∑ t ∈ T, (1 + if t = U then 2 else 0) :=
      Finset.sum_le_sum fun t ht => hp t ht
    _ ≤ T.card + 2 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one, Finset.sum_ite_eq']
      split <;> omega

/-- Connectedness outside the mixed set makes all unmixed host vertices
agree on their side, and confines every minority edge to the mixed set.
The host relation is expressed by the actual graph-edge witnesses. -/
theorem pure_one_side (U : Finset V) (E : Finset (Finset V))
    (edgeSide : Finset V → Bool) (pureSide : V → Bool) (root : V)
    (_hroot : root ∉ U)
    (hpure : ∀ v, v ∉ U → ∀ e ∈ E, v ∈ e → edgeSide e = pureSide v)
    (hconn : ∀ v, v ∉ U →
      Relation.ReflTransGen (fun x y => x ∉ U ∧ y ∉ U ∧
        ∃ e ∈ E, x ∈ e ∧ y ∈ e) root v) :
    ∀ e ∈ E, edgeSide e ≠ pureSide root → e ⊆ U := by
  have same : ∀ v, v ∉ U → pureSide root = pureSide v := by
    intro v hv
    have h := hconn v hv
    induction h with
    | refl => rfl
    | tail hxy hyz ih =>
      obtain ⟨hy, hz, e, he, hye, hze⟩ := hyz
      exact (ih hy).trans ((hpure _ hy e he hye).symm.trans (hpure _ hz e he hze))
  intro e he hmin v hv
  by_contra! hvm
  exact hmin ((hpure v hvm e he hv).trans (same v hvm).symm)

/-- Every crossing incidence is counted at most twice over its graph-edge
endpoints, even if only mixed host vertices are being counted. -/
theorem charge_le_twice {I : Type*} (U : Finset V)
    (cut : Finset I) (endpoints : I → Finset V)
    (hends : ∀ d ∈ cut, (endpoints d).card ≤ 2) :
    (∑ v ∈ U, (cut.filter (fun d => v ∈ endpoints d)).card) ≤ 2 * cut.card := by
  classical
  calc
    (∑ v ∈ U, (cut.filter (fun d => v ∈ endpoints d)).card) =
        ∑ v ∈ U, ∑ d ∈ cut, (if v ∈ endpoints d then 1 else 0 : ℕ) := by
      simp only [Finset.card_filter]
    _ = ∑ d ∈ cut, (U.filter (fun v => v ∈ endpoints d)).card := by
      rw [Finset.sum_comm]
      simp only [Finset.card_filter]
    _ ≤ ∑ _d ∈ cut, (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.card_le_card ?_).trans (hends d hd)
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    _ = 2 * cut.card := by
      simp [Nat.nsmul_eq_mul, Nat.mul_comm]

#print axioms edge_card_small
#print axioms rich_triangle
#print axioms minority_incidence
#print axioms pure_one_side
#print axioms charge_le_twice
end WagnerMinority
