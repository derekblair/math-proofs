import RefreshCollisionEntropy

namespace RefreshCollisionEntropy
open scoped BigOperators

/-- The hypothesis is exactly what sorting a probability mass by
    decreasing atoms gives: the first k values are at least y,
    all later ones at most y, and their total remains at most c. -/
theorem top_collision_bound (k l : ℕ) (f : Fin k → ℝ) (g : Fin l → ℝ)
    (c y : ℝ) (hk : 0 < k) (hy : 0 ≤ y)
    (hf : ∀ i, y ≤ f i) (hg : ∀ j, 0 ≤ g j ∧ g j ≤ y)
    (hkc : (k : ℝ) * c ≤ 1)
    (hcap : (∑ i, f i) ≤ c)
    (hnorm : (∑ i, f i) + (∑ j, g j) = 1) :
    (∑ i, (f i)^2) + (∑ j, (g j)^2) ≤ c/k := by
  let u : Fin k → ℝ := fun i => f i-y
  let U : ℝ := ∑ i, u i
  let X := U+y
  have hu (i : Fin k) : 0 ≤ u i := sub_nonneg.mpr (hf i)
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun i _ => hu i)
  have hU : U = (∑ i, f i) - (k : ℝ)*y := by
    simp [U,u,Finset.sum_sub_distrib]
  have hX : y ≤ X := by dsimp [X]; linarith
  have hcap' : X + ((k : ℝ)-1)*y ≤ c := by dsimp [X]; linarith
  have huSq : (∑ i, (u i)^2) ≤ U^2 := by
    calc
      (∑ i, (u i)^2) ≤ ∑ i, (u i)*U := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hi : u i ≤ U := Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)
        simpa [pow_two] using mul_le_mul_of_nonneg_left hi (hu i)
      _ = U^2 := by rw [← Finset.sum_mul, pow_two]
  have htail : (∑ j, (g j)^2) ≤ (∑ j, g j)*y := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      simpa [pow_two] using mul_le_mul_of_nonneg_left (hg j).2 (hg j).1
  have hfSq : (∑ i, (f i)^2) = (∑ i, (u i)^2) + 2*y*U + (k : ℝ)*y^2 := by
    have he (i : Fin k) : (f i)^2 = (u i)^2+(2*y)*(u i)+y^2 := by dsimp [u]; ring
    simp [he, Finset.sum_add_distrib, ← Finset.mul_sum, U]
  have hfinal : (∑ i, (f i)^2) + (∑ j, (g j)^2) ≤ X^2+(1-X)*y := by
    rw [hfSq]
    calc
      _ ≤ U^2 + 2*y*U + (k : ℝ)*y^2 + (∑ j, g j)*y := by linarith
      _ = X^2 + (1-X)*y := by
        have hh : U+(k : ℝ)*y+(∑ j, g j)=1 := by linarith
        have hh' := congrArg (fun z : ℝ => y*z) hh
        dsimp [X] at *
        nlinarith only [hh']
  exact hfinal.trans (concentration_bound k c y X (by exact_mod_cast hk) hy hX hkc hcap')

end RefreshCollisionEntropy
#print axioms RefreshCollisionEntropy.top_collision_bound
