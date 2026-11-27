import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Push
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace FolkmanB4.Critical
open Finset

variable {R L V : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype L] [Fintype V]
variable (I : L → V → Prop)

/-- A dichotomy of the points, with both parts meeting each specified line. -/
def Good (lines : Finset L) (color : V → Bool) : Prop :=
  ∀ l∈lines, (∃ v, I l v ∧ color v=true) ∧ (∃ v, I l v ∧ color v=false)

omit [Fintype L] in
theorem signs_of_zero {A : L → V → R} (positive : ∀ l v, I l v → 0<A l v)
    (zeros : ∀ l v, ¬I l v → A l v=0) (x : V → R) (l : L)
    (hs : ∃ v, I l v ∧ x v ≠ 0) (hz : ∑ v, A l v*x v=0) :
    (∃ v, I l v ∧ 0<x v) ∧ (∃ v, I l v ∧ x v<0) := by
  classical
  obtain ⟨w, iw, nw⟩ := hs
  constructor
  · by_contra! bad
    have nn (v : V) : A l v*x v≤0 := by
      by_cases h : I l v
      · exact mul_nonpos_of_nonneg_of_nonpos (positive l v h).le (bad v h)
      · simp [zeros l v h]
    have ww : A l w*x w<0 :=
      mul_neg_of_pos_of_neg (positive l w iw) (lt_of_le_of_ne (bad w iw) nw)
    have HH := Finset.sum_neg' (s:=univ) (fun v _ => nn v) ⟨w,mem_univ _,ww⟩
    exact (ne_of_lt HH) hz
  · by_contra! bad
    have nn (v : V) : 0≤A l v*x v := by
      by_cases h : I l v
      · exact mul_nonneg (positive l v h).le (bad v h)
      · simp [zeros l v h]
    have ww : 0<A l w*x w :=
      mul_pos (positive l w iw) (lt_of_le_of_ne (bad w iw) (Ne.symm nw))
    have HH := Finset.sum_pos' (s:=univ) (fun v _ => nn v) ⟨w,mem_univ _,ww⟩
    exact (ne_of_gt HH) hz

/-- The positive-matrix proof of the square-critical reduction: a minimum
uncolourable system has an injective incidence linear map for every choice
of strictly positive incidence weights. -/
theorem kernel_trivial (used : ∀ v, ∃ l, I l v)
    (bad : ¬∃ c, Good I univ c)
    (minimal : ∀ S : Finset L, S≠univ → ∃ c, Good I S c)
    (A : L → V → R) (positive : ∀ l v, I l v → 0<A l v)
    (zeros : ∀ l v, ¬I l v → A l v=0) (x : V → R)
    (hz : ∀ l, ∑ v, A l v*x v=0) : x=0 := by
  classical
  by_contra h
  have NX : ∃ v, x v≠0 := by
    by_contra! H
    exact h (funext H)
  obtain ⟨v,nv⟩ := NX
  obtain ⟨l,hl⟩ := used v
  let T := univ.filter fun l => ∀ v, I l v → x v=0
  have hp : T≠univ := by
    intro e
    have q : l ∈ T := by rw [e]; exact mem_univ l
    exact nv ((mem_filter.mp q).2 v hl)
  obtain ⟨c,hc⟩ := minimal T hp
  let C (v : V) := if x v=0 then c v else decide (0<x v)
  apply bad
  refine ⟨C,fun l _ => ?_⟩
  by_cases fully : ∀ v, I l v → x v=0
  · have ht : l ∈ T := mem_filter.mpr ⟨mem_univ l,fully⟩
    obtain ⟨⟨u,iu,cu⟩,⟨v,iv,cv⟩⟩ := hc l ht
    exact ⟨⟨u,iu,by simpa [C,fully u iu] using cu⟩,
      ⟨v,iv,by simpa [C,fully v iv] using cv⟩⟩
  · push Not at fully
    obtain ⟨⟨u,iu,pu⟩,⟨v,iv,pv⟩⟩ := signs_of_zero I positive zeros x l fully (hz l)
    exact ⟨⟨u,iu,by simp [C,ne_of_gt pu,pu]⟩,
      ⟨v,iv,by simp [C,ne_of_lt pv,not_lt_of_ge pv.le]⟩⟩

#print axioms kernel_trivial
end FolkmanB4.Critical
