import GeometricFolkmanConditional

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset Matrix

abbrev HostAmbient (X : ℝ) (N : ℕ) :=
  EuclideanSpace ℝ (Fin (graphDimension X (N:ℝ)))

/-- The sole remaining probabilistic input. State it as a concrete
spherical graph probability, not as an unverified axiom. -/
def CapMarginAt (t a X : ℝ) (N : ℕ) : Prop :=
  ∃ d0 : 0<graphDimension X (N:ℝ),
    letI : Nontrivial (HostAmbient X N) :=
      Module.nontrivial_of_finrank_pos (R:=ℝ) (by simpa [HostAmbient] using d0)
    Moment.mean (sphericalHostWeight (V:=Fin N) (E:=HostAmbient X N) t)
      (Moment.bad (coloringMargin a)) ≤ 1/2

noncomputable def edgeRateClosed (t : ℝ) : ℝ := -(Real.log (1-t^2))/2

/-- All of the once-subdivided-K4 Folkman construction except the cap-link
expansion input: the latter is a single explicit, checkable hypothesis.
This is not an unconditional verification of the research result. -/
theorem folkman_given_cap_margin (t a : ℝ) (t0 : 0<t) (ts : t≤1/40000) (a0 : 0<a)
    (cap : ∀ X : ℝ, 0<X → edgeRateClosed t+capRate t<X →
      ∀ B : ℝ, ∃ N : ℕ, B≤(N:ℝ) ∧ CapMarginAt t a X N) :
    ∃ N : ℕ, ∃ G' : EdgeGraph (Fin N), ¬Paraglider.Contains (hasEdge G') ∧
      ∀ c : Finset (Fin N)→Bool, ∃ tri∈triangles G', Monochrom c tri := by
  classical
  have ts' : t≤1/20000 := by linarith only [ts]
  obtain ⟨Ee,e⟩ := gram_max_exists edgeCon edgeCon_sym (by decide) t t0 ts'
  obtain ⟨Tr,tr⟩ := gram_max_exists triangleCon triangleCon_sym (by decide) t t0 ts'
  obtain ⟨Di,d⟩ := gram_max_exists diamondEdges diamond_sym (by decide) t t0 ts'
  obtain ⟨Ho,h⟩ := gram_max_exists subEdges subEdges_sym (by decide) t t0 ts'
  obtain ⟨Jo,j⟩ := gram_max_exists extCon extCon_sym (by decide) t t0 ts'
  obtain ⟨X,B,Xp,_,margin,rate⟩ := concrete_moment_error t t0 ts Ee Tr Di Ho Jo e tr d h j a a0
  have same : patternRate Ee=edgeRateClosed t := by
    unfold patternRate edgeRateClosed
    rw [edge_det_exact t t0 ts' Ee e]
  rw [same] at margin
  obtain ⟨N,large,d0,good⟩ := cap X Xp margin B
  letI : Nontrivial (HostAmbient X N) :=
    Module.nontrivial_of_finrank_pos (R:=ℝ) (by simpa [HostAmbient] using d0)
  have nc := rate N large (HostAmbient X N) (by simp [HostAmbient])
  exact ⟨N,folkman_from_concrete_margins (V:=Fin N) (E:=HostAmbient X N) t a a0 good
    (by simpa only [Fintype.card_fin] using nc)⟩

#print axioms folkman_given_cap_margin
end RobustFolkman.GeometricGap
