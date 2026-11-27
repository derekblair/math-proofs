import GeometricCommonRates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Filter
open scoped Topology

/-- A cutoff for the sum of the four quantified Chebyshev/Markov errors.
This is independent of the eventual ambient space or link good event. -/
theorem eventual_moment_error (a η : ℝ) (a0 : 0<a) (e0 : 0<η) :
    ∃ N0 : ℝ, ∀ N : ℝ, N0≤N → (768+384/a)*N^(-η)<1/2 := by
  have l : Tendsto (fun N : ℝ => (768+384/a)*N^(-η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop e0).const_mul (768+384/a)
  have ev : ∀ᶠ N : ℝ in atTop, (768+384/a)*N^(-η)<1/2 :=
    l.eventually (gt_mem_nhds (by norm_num))
  exact eventually_atTop.mp ev

/-- The four concrete pattern probabilities are sufficient for every
non-spectral strict error inequality in the finite graph reduction. -/
theorem concrete_moment_error (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (Ee : Matrix (Fin 2) (Fin 2) ℝ)
    (Tr : Matrix (Fin 2⊕Unit) (Fin 2⊕Unit) ℝ)
    (Di : Matrix Four Four ℝ) (Ho : Matrix Five Five ℝ)
    (Jo : Matrix (Five⊕Unit) (Five⊕Unit) ℝ)
    (e : GramOptimal edgeCon t Ee) (tr : GramOptimal triangleCon t Tr)
    (d : GramOptimal diamondEdges t Di) (h : GramOptimal subEdges t Ho)
    (j : GramOptimal extCon t Jo) (a : ℝ) (a0 : 0<a) :
    ∃ X N0 : ℝ, 0<X ∧ 4≤N0 ∧ patternRate Ee+capRate t<X ∧
      ∀ N : ℕ, N0≤(N:ℝ) →
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
      Module.finrank ℝ E=graphDimension X N →
      let u := (patternMass (E:=E) triangleCon t).toReal
      let v := (patternMass (E:=E) diamondEdges t).toReal
      let h := (patternMass (E:=E) subEdges t).toReal
      let j := (patternMass (E:=E) extCon t).toReal
      let C := (N.choose 3:ℝ)
      let μ := C*u
      0<μ ∧ 4/μ^2 * (C*(u+(↑(3*(N-3)) : ℝ)*v)) +
        2/(a*μ) * (3*(N:ℝ)^5*h+(N:ℝ)^6*j) < 1/2 := by
  obtain ⟨X,η,P,Xp,ηp,P1,cap,pr⟩ := joint_pattern_error_powers t t0 ts Ee Tr Di Ho Jo e tr d h j
  obtain ⟨B,bd⟩ := eventual_moment_error a η a0 ηp
  let N0 := max 4 (max P B)
  refine ⟨X,N0,Xp,le_max_left _ _,cap,?_⟩
  intro N lg E _ _ _ _ _ _ dim u v h j C μ
  have large : (4:ℝ)≤N := (le_max_left _ _).trans lg
  have nl : 4≤N := by exact_mod_cast large
  have BP : B≤(N:ℝ) := (le_max_right P B).trans ((le_max_right _ _).trans lg)
  have PP : P≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans lg)
  obtain ⟨pu,T,D,H,J⟩ := pr (N:ℝ) PP E dim
  have c : (N:ℝ)^3/48≤C := choose_three_cubic N nl
  have c0 : 0<C := (by positivity : 0<(N:ℝ)^3/48).trans_le c
  refine ⟨mul_pos c0 pu,?_⟩
  refine (moment_error_from_four N nl a u v h j ((N:ℝ)^(-η)) a0 pu
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg (by positivity) _) T D H J).trans_lt (bd N BP)

#print axioms concrete_moment_error
end RobustFolkman.GeometricGap
