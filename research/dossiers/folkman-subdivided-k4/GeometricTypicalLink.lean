import GeometricRelativeLinks
import GeometricLinkCuts

namespace RobustFolkman.GeometricGap
open Finset MeasureTheory
variable {V : Type*} [DecidableEq V] [Fintype V]

def RootCutGood (g : EdgeGraph V) (v : V) : Prop :=
  ∀ b : V → Bool, rootedLinkCut g v b ≤ (5/8)*((rootedLinkEdges g v).card:ℝ)

noncomputable def failingRoots (g : EdgeGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ¬ RootCutGood g v

theorem mem_failingRoots (g : EdgeGraph V) (v : V) :
    v∈failingRoots g ↔ ¬RootCutGood g v := by
  classical
  simp [failingRoots]

theorem failingRoots_cut (g : EdgeGraph V) (v : V) (hv : v∉failingRoots g)
    (c : Finset V → Bool) :
    linkMixedCount g c v ≤ ((1+(1:ℝ)/4)/2)*linkTriangleCount g v := by
  have good : RootCutGood g v := by by_contra! h; exact hv ((mem_failingRoots g v).2 h)
  rw [←rootedLinkCut_count,←rootedLink_count]
  convert good (fun w => c {v,w}) using 1 <;> ring

/-- For this implication only a fixed small bad-root probability is
needed, rather than a simultaneous statement over all vertices. -/
theorem typical_link_failure_reduction (p : EdgeGraph V → ℝ) (p0 : ∀ g, 0≤p g)
    (r μ : ℝ) (r0 : 0<r) (μ0 : 0<μ) (rt : (Fintype.card V:ℝ)*r=3*μ)
    (q : ∀ v, Moment.mean p (fun g => linkTriangleCount g v ^ 2) ≤ 2*r^2)
    (hp : (∑ v, Moment.mean p
        (fun g => if v∈failingRoots g then 1 else 0)) ≤ (Fintype.card V:ℝ)/(288^2))
    (var : (4/μ^2)*Moment.mean p (fun g => (((triangles g).card:ℝ)-μ)^2) ≤ 1/4) :
    Moment.mean p (Moment.bad (coloringMargin (1/32))) ≤ 1/2 := by
  classical
  have sq : (∑ v, Moment.mean p (fun g => linkTriangleCount g v ^ 2))
      ≤ (Fintype.card V:ℝ)*(2*r^2) := by
    calc
      _ ≤ ∑ _ : V, 2*r^2 := Finset.sum_le_sum (fun v _ => q v)
      _ = _ := by simp
  have w := mean_badLinkWeight_split p id failingRoots p0 (M:=288*r) (by positivity)
  have bound : Moment.mean p (fun g => badLinkWeight g (failingRoots g)) ≤ μ/64 := by
    refine w.trans ?_
    calc
      _ ≤ (1/(2*(288*r)))*((Fintype.card V:ℝ)*(2*r^2)) +
          ((288*r)/2)*((Fintype.card V:ℝ)/(288^2)) :=
        add_le_add (mul_le_mul_of_nonneg_left sq (by positivity))
          (mul_le_mul_of_nonneg_left hp (by positivity))
      _ = μ/64 := by
        field_simp [ne_of_gt r0]
        nlinarith only [rt, congrArg (fun z : ℝ => z*r) rt]
  have failure := mean_bad_coloring_weighted p id failingRoots p0 μ0 failingRoots_cut
  simp only [id_eq] at failure
  refine failure.trans ?_
  have b := mul_le_mul_of_nonneg_left bound (by positivity : 0≤12/μ)
  have numer : (12/μ)*(μ/64)=(3/16:ℝ) := by field_simp [ne_of_gt μ0]; ring
  rw [numer] at b
  linarith only [var,b]

#print axioms typical_link_failure_reduction
end RobustFolkman.GeometricGap
