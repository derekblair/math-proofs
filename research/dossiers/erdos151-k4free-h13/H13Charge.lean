import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SDiff
import Lean.Elab.Tactic.Omega

namespace H13Charge
open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

def positive (S : Finset V) (score : V → ℤ) : Finset V :=
  S.filter (fun v => 0 < score v)

def load (W : Finset V) (score : V → ℤ) (route : V → V) (v : V) : ℤ :=
  ∑ w ∈ W.filter (fun w => route w = v), score w

/-- Actual finite routing certificate: each positive score is routed to
a nonpositive vertex; capacities are deficits, and one strict capacity
gap rules out a nonnegative global score. -/
theorem strict_charge (S W : Finset V) (hw : W ⊆ S) (score : V → ℤ) (route : V → V)
    (maps : ∀ w ∈ W, route w ∈ S \ W)
    (cap : ∀ v ∈ S \ W, load W score route v ≤ -score v)
    (strict : ∃ v ∈ S \ W, load W score route v < -score v) :
    (∑ v ∈ S, score v) < 0 := by
  let T := S \ W
  have hsum := sum_fiberwise_of_maps_to (g := route) (f := score) maps
  have hl : (∑ v ∈ T, load W score route v) < ∑ v ∈ T, -score v :=
    sum_lt_sum cap strict
  change (∑ v ∈ T, load W score route v) = ∑ v ∈ W, score v at hsum
  rw [hsum,sum_neg_distrib] at hl
  rw [← sum_sdiff hw (f := score)]
  change (∑ v ∈ T, score v) + (∑ v ∈ W, score v) < 0
  omega

/-- Unit weights: the load is the number of actual clients, not an
independence or disjointness assumption on the target neighborhoods. -/
theorem unit_load (W : Finset V) (score : V → ℤ) (route : V → V) (v : V)
    (unit : ∀ w ∈ W, score w = 1) :
    load W score route v = ((W.filter (fun w => route w = v)).card : ℤ) := by
  unfold load
  calc
    _ = ∑ _w ∈ W.filter (fun w => route w = v), (1 : ℤ) :=
      sum_congr rfl (fun w hw => unit w (mem_filter.mp hw).1)
    _ = _ := by simp

/-- A reusable n63 endpoint. Missing target vertices have zero load,
so one may check strict caps only at vertices that receive a client. -/
theorem unit_routing_forces_neutral (S : Finset V) (score : V → ℤ) (route : V → V)
    (unit : ∀ w ∈ S, 0 < score w → score w = 1)
    (maps : ∀ w ∈ S, 0 < score w → route w ∈ S ∧ score (route w) ≤ 0)
    (strict : ∀ v ∈ S,
      (∃ w ∈ S, 0 < score w ∧ route w = v) →
      (((positive S score).filter (fun w => route w = v)).card : ℤ) < -score v)
    (global : 0 ≤ ∑ v ∈ S, score v) :
    ∀ v ∈ S, score v = 0 := by
  classical
  let W := positive S score
  let T := S \ W
  have mapT : ∀ w ∈ W, route w ∈ T := by
    intro w hw
    have h := mem_filter.mp hw
    have hh := maps w h.1 h.2
    exact mem_sdiff.mpr ⟨hh.1,fun hv => (not_lt_of_ge hh.2) (mem_filter.mp hv).2⟩
  have loadEq (v : V) :
      load W score route v = ((W.filter (fun w => route w = v)).card : ℤ) :=
    unit_load W score route v (fun w hw => unit w (mem_filter.mp hw).1 (mem_filter.mp hw).2)
  have capT : ∀ v ∈ T, load W score route v ≤ -score v := by
    intro v hv
    have hv' := mem_sdiff.mp hv
    have hnon : score v ≤ 0 := le_of_not_gt (fun h => hv'.2 (mem_filter.mpr ⟨hv'.1,h⟩))
    by_cases h : (W.filter (fun w => route w = v)).Nonempty
    · obtain ⟨w,hw⟩ := h
      have hw' := mem_filter.mp hw
      have hcap := strict v hv'.1 ⟨w,(mem_filter.mp hw'.1).1,(mem_filter.mp hw'.1).2,hw'.2⟩
      rw [loadEq]
      exact le_of_lt hcap
    · rw [loadEq,not_nonempty_iff_eq_empty.mp h]
      simpa using (neg_nonneg.mpr hnon)
  have noW : ∀ w ∈ S, ¬0 < score w := by
    intro w hw hp
    have hwW : w ∈ W := mem_filter.mpr ⟨hw,hp⟩
    have ht := mapT w hwW
    have hh := strict (route w) (mem_sdiff.mp ht).1 ⟨w,hw,hp,rfl⟩
    have hstrict : ∃ v ∈ T, load W score route v < -score v :=
      ⟨route w,ht,by rw [loadEq]; exact hh⟩
    exact (not_lt_of_ge global) (strict_charge S W (filter_subset _ _) score route mapT capT hstrict)
  intro v hv
  have hle : score v ≤ 0 := le_of_not_gt (noW v hv)
  by_contra hn
  have hlt : score v < 0 := lt_of_le_of_ne hle hn
  have hsum : (∑ v ∈ S, score v) < ∑ _v ∈ S, (0 : ℤ) :=
    sum_lt_sum (fun y hy => le_of_not_gt (noW y hy)) ⟨v,hv,hlt⟩
  simp only [sum_const_zero] at hsum
  exact (not_lt_of_ge global) hsum

#print axioms strict_charge
#print axioms unit_load
#print axioms unit_routing_forces_neutral
end H13Charge
