import GeometricDecoupledNorm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Real.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NoncommRing

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

def weightedMatrix (w : I→ℝ) (A : I→Matrix J J ℝ) : Matrix J J ℝ :=
  ∑ i, w i • A i

def rankOneMat (v : J→ℝ) : Matrix J J ℝ :=
  Matrix.vecMulVec v v

theorem rankOneMat_psd (v : J→ℝ) : (rankOneMat v).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star v

theorem rankOneMat_square (v : J→ℝ) :
    (rankOneMat v)^2 = (∑ j, (v j)^2) • rankOneMat v := by
  ext i j
  simp only [pow_two,rankOneMat,Matrix.mul_apply,Matrix.vecMulVec_apply,Matrix.smul_apply,smul_eq_mul]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem weightedMatrix_psd (w : I→ℝ) (A : I→Matrix J J ℝ) (w0 : ∀ i, 0≤w i)
    (h : ∀ i, (A i).PosSemidef) : (weightedMatrix w A).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => (h i).smul (w0 i)

theorem hermitian_square_psd {M : Matrix J J ℝ} (h : M.IsHermitian) : (M^2).PosSemidef := by
  rw [pow_two]
  simpa only [h.eq] using Matrix.posSemidef_self_mul_conjTranspose M

theorem weighted_centered_square (w : I→ℝ) (C : I→Matrix J J ℝ) (w1 : ∑ i, w i=1) :
    let M := weightedMatrix w C
    weightedMatrix w (fun i => (C i-M)^2) = weightedMatrix w (fun i => (C i)^2) - M^2 := by
  intro M
  have e (i : I) : (C i-M)^2 = C i^2 - C i*M - M*C i + M^2 := by noncomm_ring
  have l : (∑ i, w i • (C i*M)) = M^2 := by
    simp only [←Matrix.smul_mul,←Finset.sum_mul,pow_two]
    rfl
  have r : (∑ i, w i • (M*C i)) = M^2 := by
    simp only [←Matrix.mul_smul,←Finset.mul_sum,pow_two]
    rfl
  have h : (∑ i, w i • M^2)=M^2 := by rw [←Finset.sum_smul,w1,one_smul]
  unfold weightedMatrix
  simp_rw [e,smul_add,smul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [l,r,h]
  abel

/-- Finite rank-one covariance variance proxy. Both inequalities are
Loewner inequalities, expressed as positive semidefinite differences. -/
theorem weighted_rank_one_variance (w : I→ℝ) (v : I→J→ℝ) (K : ℝ)
    (w0 : ∀ i, 0≤w i) (w1 : ∑ i,w i=1)
    (bound : ∀ i, ∑ j, (v i j)^2≤K) :
    let C := fun i => rankOneMat (v i)
    let M := weightedMatrix w C
    let V := weightedMatrix w (fun i => (C i-M)^2)
    V.PosSemidef ∧ ((K • M)-V).PosSemidef := by
  intro C M V
  have ps (i : I) : (C i).PosSemidef := rankOneMat_psd _
  have mp : M.PosSemidef := weightedMatrix_psd w C w0 ps
  have Vp : V.PosSemidef := weightedMatrix_psd w _ w0 (fun i =>
    hermitian_square_psd ((ps i).isHermitian.sub mp.isHermitian))
  refine ⟨Vp,?_⟩
  have z (i : I) : ((K • C i)-(C i)^2).PosSemidef := by
    rw [show (C i)^2 = (∑ j, (v i j)^2) • C i from rankOneMat_square _,
      ←sub_smul]
    exact (ps i).smul (sub_nonneg.mpr (bound i))
  have eq : weightedMatrix w (fun i => (K • C i)-(C i)^2) =
      K • M - weightedMatrix w (fun i => (C i)^2) := by
    unfold weightedMatrix
    simp_rw [smul_sub,Finset.sum_sub_distrib,smul_comm (w _),←Finset.smul_sum]
    rfl
  have h := (weightedMatrix_psd w _ w0 z).add (hermitian_square_psd mp.isHermitian)
  rw [eq] at h
  convert h using 1
  change K • M - weightedMatrix w (fun i => (C i-M)^2) = _
  rw [weighted_centered_square w C w1]
  abel

#print axioms weighted_rank_one_variance
end RobustFolkman.GeometricGap
