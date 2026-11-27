import GeometricRootedVariance

namespace RobustFolkman.GeometricGap
open Finset MeasureTheory
variable {V E : Type*} [DecidableEq V] [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]

theorem rootedLink_secondMoment (t : ℝ) (v : V) :
    let u := (patternMass (E:=E) triangleCon t).toReal
    let q := (patternMass (E:=E) diamondEdges t).toReal
    let A : ℝ := (Fintype.card V-1).choose 2
    Moment.mean (sphericalHostWeight (E:=E) t) (fun g => linkTriangleCount g v ^ 2) ≤
      (A*u)^2 + A*(u+(↑(3*(Fintype.card V-3)):ℝ)*q) := by
  intro u q A
  let p := sphericalHostWeight (V:=V) (E:=E) t
  let f := fun g => linkTriangleCount g v
  have mean : Moment.mean p f=A*u := rootedLink_mean (E:=E) t v
  have cov := Moment.mean_covariance p
    (sphericalHostWeight_probability (V:=V) (E:=E) t).2 f f
  rw [mean] at cov
  simp only [←pow_two] at cov
  have h := rootedLink_variance (E:=E) t v
  change Moment.mean p (fun g => (f g - A*u)^2) ≤ A*(u+(↑(3*(Fintype.card V-3)):ℝ)*q) at h
  rw [cov] at h
  change Moment.mean p (fun g => f g ^ 2) ≤ _
  linarith only [h]

#print axioms rootedLink_secondMoment
end RobustFolkman.GeometricGap
