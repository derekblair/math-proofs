import Cardinal

namespace PermCircles
open Real

lemma radius_le_order {r : ℝ} {n : ℕ} (hr : 0 ≤ r) (h : Fits r n) :
    r ≤ (n : ℝ) := by
  rcases h with ⟨hn,p,hp⟩
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hne : i ≠ j := by intro e; have hh := congrArg Fin.val e; norm_num [i,j] at hh
  have hd := hp i j hne
  have hp0 : 0 ≤ ((p i).val : ℝ) := by positivity
  have hp1 : 0 ≤ ((p j).val : ℝ) := by positivity
  have hi : ((p i).val : ℝ) < n := by exact_mod_cast (p i).isLt
  have hj : ((p j).val : ℝ) < n := by exact_mod_cast (p j).isLt
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  simp only [i,j, Nat.cast_zero,Nat.cast_one] at hd
  have hm : 0 ≤ ((n:ℝ)-((p i).val-(p j).val))*((n:ℝ)+((p i).val-(p j).val)) :=
    mul_nonneg (by linarith) (by linarith)
  by_contra! hh
  nlinarith [mul_nonneg (show 0 ≤ r-n by linarith) (show 0 ≤ r+n by linarith),
    mul_nonneg (show 0 ≤ (n:ℝ)-1 by linarith) (show 0 ≤ (n:ℝ)+1 by linarith)]

/-- Turn a sharp finite packing bound (area of clipped Voronoi cells) into
    a lower bound on the board size with a linear boundary error. -/
lemma finite_to_order_lower {r : ℝ} (hr : 1 ≤ r) {n : ℕ} (h : Fits r n)
    (harea : 2*sqrt 3*(n:ℝ)*r^2 ≤ ((n:ℝ)+4*r/sqrt 3)^2) :
    2*sqrt 3*r^2-(8/sqrt 3+16/3)*r ≤ n := by
  have hn := radius_le_order (by linarith) h
  have hnp : 0 < (n:ℝ) := by linarith
  let K := sqrt 3
  have hK : 0 < K := sqrt_pos.2 (by norm_num)
  have hK2 : K^2=3 := sq_sqrt (by norm_num)
  change 2*K*(n:ℝ)*r^2 ≤ ((n:ℝ)+4*r/K)^2 at harea
  change 2*K*r^2-(8/K+16/3)*r ≤ n
  have he : (4*r/K)^2 = (16/3)*r^2 := by
    rw [div_pow,hK2]
    ring
  have hexp : ((n:ℝ)+4*r/K)^2 =
      (n:ℝ)^2 + (8/K)*r*n+(16/3)*r^2 := by
    calc
      _ = (n:ℝ)^2 + 2*(n:ℝ)*(4*r/K)+(4*r/K)^2 := by ring
      _ = _ := by rw [he]; ring
  have hrn := mul_nonneg (show 0 ≤ (16/3:ℝ)*r by positivity) (show 0 ≤ (n:ℝ)-r by linarith)
  apply (mul_le_mul_iff_left₀ hnp).mp
  rw [hexp] at harea
  nlinarith only [harea,hrn]

#print axioms finite_to_order_lower
end PermCircles
