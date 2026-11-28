import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Lean.Elab.Tactic.Omega

open scoped BigOperators
namespace Erdős151.H12

variable {V E : Type*} [Fintype V] [Fintype E]

private def incidenceLin (edge : E → Finset V) : (V → ℚ) →ₗ[ℚ] (E → ℚ) where
  toFun f e := ∑ v ∈ edge e, f v
  map_add' f g := by ext e; exact Finset.sum_add_distrib
  map_smul' q f := by ext e; simp [smul_eq_mul, Finset.mul_sum]

private theorem nonzero_zero_sums (edge : E → Finset V)
    (h : Fintype.card E < Fintype.card V) :
    ∃ f : V → ℚ, (∃ v, f v ≠ 0) ∧ ∀ e, (∑ v ∈ edge e, f v) = 0 := by
  let L := incidenceLin edge
  have ni : ¬ Function.Injective L := by
    intro hi
    have h' := LinearMap.finrank_le_finrank_of_injective hi
    have hh : Fintype.card V ≤ Fintype.card E := by
      simpa only [Module.finrank_fintype_fun_eq_card] using h'
    exact (not_le_of_gt h) hh
  unfold Function.Injective at ni
  push Not at ni
  obtain ⟨f,g,hfg,hne⟩ := ni
  let d := f-g
  have dn : d ≠ 0 := sub_ne_zero.mpr hne
  have vz : ∃ v, d v ≠ 0 := by
    by_contra! hh
    exact dn (funext hh)
  have hzero : L d = 0 := by rw [map_sub, hfg, sub_self]
  exact ⟨d,vz,fun e => congrFun hzero e⟩

theorem both_signs {f : V → ℚ} {s : Finset V}
    (hz : (∑ v ∈ s, f v) = 0) (hn : ∃ v ∈ s, f v ≠ 0) :
    (∃ v ∈ s, 0 < f v) ∧ (∃ v ∈ s, f v < 0) := by
  obtain ⟨a,ha,hna⟩ := hn
  constructor
  · by_contra! h
    have al : 0 < -f a := neg_pos.mpr (lt_of_le_of_ne (h a ha) hna)
    have sh : -f a ≤ ∑ x ∈ s, -f x :=
      Finset.single_le_sum (fun b hb => neg_nonneg.mpr (h b hb)) ha
    rw [Finset.sum_neg_distrib, hz, neg_zero] at sh
    exact (not_le_of_gt al) sh
  · by_contra! h
    have al : 0 < f a := lt_of_le_of_ne (h a ha) (Ne.symm hna)
    have sh : f a ≤ ∑ x ∈ s, f x := Finset.single_le_sum h ha
    rw [hz] at sh
    exact (not_le_of_gt al) sh

def Mixed (c : V → Bool) (s : Finset V) : Prop :=
    (∃ x ∈ s, c x = true) ∧ (∃ y ∈ s, c y = false)

/-- Lovász–Woodall–Seymour critical hypergraph density. Every
non-isolated vertex counts, and the hypotheses ask for edge-criticality
rather than imposing any rank, linearity, or uniformity. -/
theorem critical_hypergraph_density (edge : E → Finset V)
    (uses : ∀ v, ∃ e, v ∈ edge e)
    (critical : ∀ e, ∃ c : V → Bool, ∀ i, i ≠ e → Mixed c (edge i))
    (bad : ¬ ∃ c : V → Bool, ∀ e, Mixed c (edge e)) :
    Fintype.card V ≤ Fintype.card E := by
  classical
  by_contra! h
  obtain ⟨f,⟨v,hv⟩,zeros⟩ := nonzero_zero_sums edge h
  obtain ⟨e,he⟩ := uses v
  obtain ⟨old,works⟩ := critical e
  let c (x : V) : Bool := if 0 < f x then true else if f x < 0 then false else old x
  apply bad
  refine ⟨c,fun i => ?_⟩
  by_cases hi : ∃ z ∈ edge i, f z ≠ 0
  · obtain ⟨⟨u,hu,hup⟩,⟨w,hw,hwn⟩⟩ := both_signs (zeros i) hi
    exact ⟨⟨u,hu,by simp [c,hup]⟩,⟨w,hw,by simp [c,hwn,not_lt_of_ge hwn.le]⟩⟩
  · push Not at hi
    have ine : i ≠ e := by
      intro q
      subst i
      exact hv (hi v he)
    obtain ⟨⟨u,hu,hup⟩,⟨w,hw,hwn⟩⟩ := works i ine
    exact ⟨⟨u,hu,by simp [c,hi u hu,hup]⟩,⟨w,hw,by simp [c,hi w hw,hwn]⟩⟩

/-- It is enough that every noncolorable subfamily uses all vertices.
An inclusion-minimal noncolorable edge subfamily is then edge-critical
on the same vertex type. -/
theorem density_of_full_support_obstructions (edge : E → Finset V)
    (bad : ¬ ∃ c : V → Bool, ∀ e, Mixed c (edge e))
    (full : ∀ A : Finset E, (¬ ∃ c : V → Bool, ∀ e ∈ A, Mixed c (edge e)) →
      ∀ v, ∃ e ∈ A, v ∈ edge e) :
    Fintype.card V ≤ Fintype.card E := by
  classical
  let Bad := fun A : Finset E => ¬ ∃ c : V → Bool, ∀ e ∈ A, Mixed c (edge e)
  have univbad : Bad Finset.univ := by simpa [Bad] using bad
  have existsBad : ∃ n, ∃ A : Finset E, Bad A ∧ A.card = n :=
    ⟨_,Finset.univ,univbad,rfl⟩
  obtain ⟨A,ha,asize⟩ := Nat.find_spec existsBad
  have small (e : E) (he : e ∈ A) : ¬ Bad (A.erase e) := by
    intro hf
    have hm := Nat.find_min' existsBad ⟨A.erase e,hf,rfl⟩
    rw [Finset.card_erase_of_mem he, asize] at hm
    have hap : 1 ≤ A.card := Finset.card_pos.mpr ⟨e,he⟩
    omega
  have u (v : V) : ∃ e : ↥A, v ∈ edge e := by
    obtain ⟨e,he,hv⟩ := full A ha v
    exact ⟨⟨e,he⟩,hv⟩
  have nb : ¬ ∃ c : V → Bool, ∀ e : ↥A, Mixed c (edge e) := by
    rintro ⟨c,hc⟩
    exact ha ⟨c,fun i hi => hc ⟨i,hi⟩⟩
  have cr (e : ↥A) : ∃ c : V → Bool, ∀ i : ↥A, i ≠ e → Mixed c (edge i) := by
    have h := small e.val e.property
    dsimp [Bad] at h
    obtain ⟨c,hc⟩ := Classical.not_not.mp h
    refine ⟨c,fun i hi => hc i (Finset.mem_erase.mpr ⟨?_,i.property⟩)⟩
    exact fun he => hi (Subtype.ext he)
  have h1 := critical_hypergraph_density (fun e : ↥A => edge e) u cr nb
  rw [Fintype.card_coe] at h1
  have h2 : A.card ≤ Fintype.card E := Finset.card_le_univ A
  omega

#print axioms density_of_full_support_obstructions
#print axioms critical_hypergraph_density
end Erdős151.H12
