import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace RobustFolkman.Moment
open Finset
variable {Ω 𝕜 : Type*} [Fintype Ω] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

def mean (p f : Ω → 𝕜) : 𝕜 := ∑ ω, p ω*f ω

def bad (good : Ω → Bool) (ω : Ω) : 𝕜 := if good ω then 0 else 1

def score (good : Ω → Bool) (T C : Ω → 𝕜) (μ a : 𝕜) (ω : Ω) : 𝕜 :=
  bad good ω + (4/μ^2)*(T ω-μ)^2 + (2/(a*μ))*C ω

theorem mean_score (p : Ω → 𝕜) (good : Ω → Bool) (T C : Ω → 𝕜) (μ a : 𝕜) :
    mean p (score good T C μ a) =
      mean p (bad good)+(4/μ^2)*mean p (fun k => (T k-μ)^2)+(2/(a*μ))*mean p C := by
  unfold mean score
  simp only [mul_add,sum_add_distrib]
  have v : (∑ x, p x*(4/μ^2*(T x-μ)^2))=4/μ^2*(∑ x,p x*(T x-μ)^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  have d : (∑ x,p x*(2/(a*μ)*C x))=2/(a*μ)*(∑ x,p x*C x) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  rw [v,d]

/-- A finite distribution admits one graph with a positive triangle
margin if the variance, deletion charge, and exceptional spectral mass
satisfy one quantitative inequality. No independence assumptions. -/
theorem select_good (p : Ω → 𝕜) (hp : ∀ ω, 0≤p ω) (p1 : (∑ ω,p ω)=1)
    (good : Ω → Bool) (T C : Ω → 𝕜) (C0 : ∀ ω, 0≤C ω) (μ a : 𝕜)
    (μ0 : 0<μ) (a0 : 0<a)
    (bound : mean p (bad good)+(4/μ^2)*mean p (fun k => (T k-μ)^2)
      +(2/(a*μ))*mean p C<1) :
    ∃ ω, good ω=true ∧ μ/2<T ω ∧ C ω<a*T ω := by
  have less : mean p (score good T C μ a)<1 := (mean_score p good T C μ a).symm ▸ bound
  have existsLow : ∃ ω, score good T C μ a ω<1 := by
    by_contra! none
    have b : (∑ ω,p ω)≤mean p (score good T C μ a) := by
      unfold mean
      apply sum_le_sum
      intro ω _
      exact (mul_one (p ω)).symm.trans_le (mul_le_mul_of_nonneg_left (none ω) (hp ω))
    linarith only [p1,b,less]
  obtain ⟨ω,hω⟩ := existsLow
  have B0 : 0≤(bad good ω : 𝕜) := by unfold bad; split <;> positivity
  have V0 : 0≤(4/μ^2)*(T ω-μ)^2 := by positivity
  have D0 : 0≤(2/(a*μ))*C ω := mul_nonneg (by positivity) (C0 ω)
  unfold score at hω
  have ok : good ω=true := by
    cases h : good ω
    · have bad1 : (bad good ω : 𝕜)=1 := by simp [bad,h]
      linarith only [hω,bad1,V0,D0]
    · rfl
  have varLt : (4/μ^2)*(T ω-μ)^2<1 := by linarith only [hω,B0,D0]
  have varLt' : 4*(T ω-μ)^2<μ^2 := by
    have g := mul_lt_mul_of_pos_right varLt (show 0<μ^2 by positivity)
    convert g using 1 <;> field_simp
  have big : μ/2<T ω := by
    by_contra! no
    have c := mul_nonneg (show 0≤μ/2-T ω by linarith)
      (show 0≤ μ-T ω+μ/2 by linarith)
    nlinarith only [c,varLt']
  have costLt : (2/(a*μ))*C ω<1 := by linarith only [hω,B0,V0]
  have costLt' : 2*C ω<a*μ := by
    have g := mul_lt_mul_of_pos_right costLt (mul_pos a0 μ0)
    convert g using 1 <;> field_simp
  have big' := mul_lt_mul_of_pos_left big a0
  exact ⟨ω,ok,big,by linarith only [costLt',big']⟩

#print axioms select_good
end RobustFolkman.Moment
