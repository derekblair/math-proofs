import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
open scoped BigOperators
namespace PetersenStability

noncomputable def term (s u v : ℝ) : ℝ :=
  (1/2-s-u-v/4)*(s/3+v/4)

/-- Certificate independent of the chart geometry. The three marginal sums
are the only chart incidences needed for this quadratic bound. -/
theorem cost_bound (s u v : Fin 20 → ℝ) (Y : ℝ) (hY : 0 ≤ Y)
    (hs : ∀ j, (3/10-3/90 : ℝ) ≤ s j)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (hS : ∑ j, s j = 6*(1-Y)) (hU : ∑ j, u j = 4*Y)
    (hV : ∑ j, v j = 4*Y) :
    ∑ j, term (s j) (u j) (v j) ≤ 2/5 := by
  let m : ℝ := 3/10*(1-Y)
  have hm : 0 ≤ ∑ j : Fin 20, (s j-m)^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : (∑ j : Fin 20, (s j-m)^2) =
      (∑ j, (s j)^2) - 2*m*(∑ j,s j) + 20*m^2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hh : (∑ j : Fin 20, 2*s j*m) = 2*m*(∑ j,s j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hh]
    norm_num
  have hq : (20*m^2 : ℝ) ≤ ∑ j, (s j)^2 := by
    rw [he, hS] at hm
    dsimp [m] at *
    nlinarith
  have hint (j : Fin 20) :
      term (s j) (u j) (v j) ≤
      s j/6 - (s j)^2/3 + v j/8 - (u j+v j)*(3/10-3/90)/3 := by
    have h1 := mul_nonneg (add_nonneg (hu j) (hv j)) (sub_nonneg.mpr (hs j))
    have h2 := mul_nonneg (hv j) (add_nonneg (hu j) (div_nonneg (hv j) (by norm_num : (0:ℝ) ≤ 4)))
    unfold term
    nlinarith
  calc
    _ ≤ ∑ j, (s j/6 - (s j)^2/3 + v j/8 -
        (u j+v j)*(3/10-3/90)/3) := Finset.sum_le_sum fun j _ => hint j
    _ = (∑ j, s j)/6 - (∑ j,(s j)^2)/3 + (∑ j,v j)/8 -
        ((∑ j,u j)+(∑ j,v j))*(3/10-3/90)/3 := by
      simp_rw [div_eq_mul_inv]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul]
    _ ≤ _ := by
      rw [hS, hU, hV]
      dsimp [m] at hq
      nlinarith [sq_nonneg Y]
#print axioms cost_bound
end PetersenStability
