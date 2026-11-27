import GeometricTriangleCorr
import GeometricQuantitativeAssembly
import GeometricPatternAssembly

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset Matrix
variable {V E : Type*} [DecidableEq V] [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def coloringMargin (a : ℝ) (g : EdgeGraph V) : Bool := by
  classical
  exact decide (∀ c : Finset V→Bool,
    a*((triangles g).card:ℝ)≤((mono (triangles g) c).card:ℝ))

/-- All non-spectral parts of the Folkman construction, including actual
joint triangle moments and deletion charges, are assembled here. -/
theorem folkman_from_concrete_margins (t a : ℝ) (a0 : 0<a)
    (spectral : Moment.mean (sphericalHostWeight (V:=V) (E:=E) t)
      (Moment.bad (coloringMargin a)) ≤ 1/2)
    (numeric :
      let u := (patternMass (E:=E) triangleCon t).toReal
      let v := (patternMass (E:=E) diamondEdges t).toReal
      let h := (patternMass (E:=E) subEdges t).toReal
      let j := (patternMass (E:=E) extCon t).toReal
      let N := Fintype.card V
      let C := (N.choose 3:ℝ)
      let μ := C*u
      0<μ ∧ 4/μ^2 * (C*(u+(↑(3*(N-3)) : ℝ)*v)) +
        2/(a*μ) * (3*(N:ℝ)^5*h+(N:ℝ)^6*j) < 1/2) :
    ∃ G' : EdgeGraph V, ¬Paraglider.Contains (hasEdge G') ∧
      ∀ c : Finset V→Bool, ∃ tri∈triangles G', Monochrom c tri := by
  classical
  let u := (patternMass (E:=E) triangleCon t).toReal
  let v := (patternMass (E:=E) diamondEdges t).toReal
  let h := (patternMass (E:=E) subEdges t).toReal
  let j := (patternMass (E:=E) extCon t).toReal
  let p : EdgeGraph V→ℝ := sphericalHostWeight (E:=E) t
  have ⟨p0,p1⟩ := sphericalHostWeight_probability (V:=V) (E:=E) t
  have sc (s : Finset V) (hs : s∈(univ : Finset V).powersetCard 3) : s.card=3 :=
    (Finset.mem_powersetCard.mp hs).2
  apply from_pattern_probabilities p p0 p1 id (coloringMargin a) a u v h j a0
    ENNReal.toReal_nonneg numeric.1
  · intro s hs
    exact triangle_moment_exact t s (sc s hs)
  · intro r s hr hs ne inter
    exact (nonedge_overlap_triangle_moments t r s (sc r hr) (sc s hs) ne inter).le
  · intro r s hr hs _ inter
    exact (diamond_moment_overlap_two t r s (sc r hr) (sc s hs) inter).le
  · exact forbidden_moment_bound t
  · exact extension_moment_bound t
  · intro g gg
    unfold coloringMargin at gg
    exact of_decide_eq_true gg
  · dsimp only
    have nn := numeric.2
    nlinarith only [spectral,nn]

#print axioms folkman_from_concrete_margins
end RobustFolkman.GeometricGap
