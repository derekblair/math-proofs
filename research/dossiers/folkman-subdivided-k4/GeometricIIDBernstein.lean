import GeometricFiniteBernstein
import GeometricKernelCovariance
import Mathlib.MeasureTheory.Constructions.Pi

namespace RobustFolkman.GeometricGap
open MeasureTheory ProbabilityTheory Matrix Finset RMT
open scoped ENNReal Matrix.Norms.L2Operator
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem iid_finite_rank_one_bernstein {n N : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : Ω→Fin n→ℝ) (K T s : ℝ) (Kp : 0<K) (T0 : 0≤T) (sp : 0<s)
    (hn : 0<n) (bounded : ∀ ω, ∑ j, (v ω j)^2≤K)
    (meanBound : ‖finiteMatrixMean μ (fun ω => rankOneMat (v ω))‖≤T) :
    ((Measure.pi (fun _ : Fin N => μ))
      {x | ‖(∑ i,rankOneMat (v (x i))) - (N:ℝ) •
        finiteMatrixMean μ (fun ω => rankOneMat (v ω))‖≥s}).toReal ≤
      matrixBernsteinTailBound n ((N:ℝ)*K*T) (K+T) s := by
  let ν := Measure.pi (fun _ : Fin N => μ)
  let C := fun ω => rankOneMat (v ω)
  let M := finiteMatrixMean μ C
  have Tmean (i : Fin N) : finiteMatrixMean ν (fun x => C (x i))=M := by
    change _=finiteMatrixMean μ C
    rw [←finiteMatrixMean_integral ν,←finiteMatrixMean_integral μ]
    have f := measurePreserving_eval (μ:=fun _ : Fin N => μ) i
    rw [← f.map_eq, integral_map f.aemeasurable Integrable.of_finite.aestronglyMeasurable]
  have Tc (i : Fin N) (x : Fin N→Ω) :
      centeredRankOne ν (fun x => v (x i)) x = C (x i)-M := by
    unfold centeredRankOne
    rw [Tmean]
  have id : MatrixBernsteinIndependent (fun i => centeredRankOne ν (fun x => v (x i))) ν := by
    have all : (fun (i : Fin N) (x : Fin N→Ω) => centeredRankOne ν (fun x => v (x i)) x) =
        fun i x => C (x i)-M := by funext i x; exact Tc i x
    rw [all]
    unfold MatrixBernsteinIndependent
    letI : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
    exact iIndepFun_pi (μ:=fun _ : Fin N => μ) (X:=fun _ ω => C ω-M)
      (fun _ => (measurable_of_finite _).aemeasurable)
  have applyB := finite_rank_one_bernstein ν (fun (i : Fin N) (x : Fin N→Ω) => v (x i))
    K T s Kp T0 sp hn (fun i x => bounded (x i))
    (fun i => by rw [Tmean]; exact meanBound) id
  have eq (x : Fin N→Ω) :
      (∑ i : Fin N, centeredRankOne ν (fun z => v (z i)) x) =
        (∑ i : Fin N, C (x i))-(N:ℝ) • M := by
    simp_rw [Tc,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
  simp_rw [eq] at applyB
  exact applyB

theorem iid_feature_covariance_tail {D N : ℕ} (μ : Measure (Fin D)) [IsProbabilityMeasure μ]
    (K : Fin D→Fin D→ℝ) (B ρ s : ℝ) (Bp : 0<B) (ρ0 : 0≤ρ) (sp : 0<s) (hd : 0<D)
    (bound : ∀ x, ∑ j,(kernelFeature K (fun ω => (μ {ω}).toReal) x j)^2≤B)
    (pop : ‖weightedKernel K (fun ω => (μ {ω}).toReal)‖≤ρ) :
    let p := fun ω => (μ {ω}).toReal
    let M := weightedMatrix p (fun x => rankOneMat (kernelFeature K p x))
    ((Measure.pi fun _ : Fin N => μ)
      {x | ‖(∑ i,rankOneMat (kernelFeature K p (x i))) - (N:ℝ) • M‖≥s}).toReal ≤
        matrixBernsteinTailBound D ((N:ℝ)*B*ρ^2) (B+ρ^2) s := by
  intro p M
  have h : ‖M‖≤ρ^2 := by
    rw [show M=weightedMatrix p (fun x => rankOneMat (kernelFeature K p x)) from rfl,
      kernel_feature_population_norm K p (fun _ => ENNReal.toReal_nonneg)]
    exact pow_le_pow_left₀ (norm_nonneg _) pop 2
  exact iid_finite_rank_one_bernstein μ (kernelFeature K p) B (ρ^2) s Bp (sq_nonneg _) sp hd bound h

#print axioms iid_finite_rank_one_bernstein
#print axioms iid_feature_covariance_tail
end RobustFolkman.GeometricGap
