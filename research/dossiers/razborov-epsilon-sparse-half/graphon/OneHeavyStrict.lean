import CountableHeavy

namespace SparseHalfCountableEndpoint
open SparseHalfLowSmallSide SparseHalfOneHeavyNormalized

/-- At the endpoint, a genuine single heavy block away from full capacity
cannot make the sharp half bound tight. -/
theorem one_heavy_strict_scalar (θ u : ℝ) (hθ : 1≤θ) (hθ' : θ≤2)
    (hu : 2<u) (hu' : u<4) :
    min (u^2/4) (θ*u/2)+base θ u-θ<2 := by
  have hmon : min (u^2/4) (θ*u/2) - θ≤u^2/4-u/2 := by
    by_cases hj : u/2≤θ
    · have hh := min_le_left (u^2/4) (θ*u/2); linarith
    · have hh := min_le_right (u^2/4) (θ*u/2)
      have hp := mul_nonneg (show 0≤u/2-θ by linarith) (show 0≤u/2-1 by linarith)
      nlinarith
  unfold base
  by_cases h : 8-2*u≤θ+1
  · rw [ite_eq_left h]
    by_cases hu3 : 3≤u
    · rw [eq_small _ (by linarith : 8-2*u≤2)]
      have f := mul_nonneg (show 0≤u-3 by linarith) (show 0≤4-u by linarith)
      nlinarith
    · rw [eq_large _ (by linarith : 2≤8-2*u)]
      by_cases ha : u≤14/5
      · have hm := min_le_left (u^2/4) (θ*u/2)
        have hsq := mul_nonneg (show 0≤14/5-u by linarith) (show 0≤14/5+u by linarith)
        nlinarith
      · have hp := mul_nonneg (show 0≤u-14/5 by linarith) (show 0≤3-u by linarith)
        nlinarith
  · rw [ite_eq_right h, eq_small _ (by linarith : 7-2*u-θ≤2)]
    have hu3 : u<3 := by linarith
    let L := 7-2*u
    have hLt : θ≤L := by dsimp [L]; linarith
    have hF1 : 1*u/2+(L-1)^2/4<2 := by
      dsimp [L]
      have hp := mul_pos (show 0<u-2 by linarith) (show 0<3-u by linarith)
      nlinarith
    have hFu (huL : u/2≤L) : u^2/4+(L-u/2)^2/4<2 := by
      have h2 : u≤14/5 := by dsimp [L] at huL; linarith
      have hp := mul_nonneg (show 0≤u-2 by linarith) (show 0≤14/5-u by linarith)
      dsimp [L]
      nlinarith
    by_cases ho : u/2≤θ
    · have hm := min_le_left (u^2/4) (θ*u/2)
      have hp := mul_nonneg (show 0≤θ-u/2 by linarith) (show 0≤2*L-u/2-θ by linarith)
      change min (u^2/4) (θ*u/2)+(θ+(L-θ)^2/4)-θ<2
      nlinarith [hFu (ho.trans hLt)]
    · let b := min (u/2) L
      have hb : θ≤b := le_min (by linarith) hLt
      have hb1 : 1≤b := hθ.trans hb
      have hFb : b*u/2+(L-b)^2/4<2 := by
        by_cases hj : u/2≤L
        · dsimp [b]
          rw [min_eq_left hj]
          nlinarith [hFu hj]
        · have hL' : L≤u/2 := by linarith
          have huL : 14/5≤u := by dsimp [L] at hL'; linarith
          have hp := mul_nonneg (show 0≤u-14/5 by linarith) (show 0≤2*u-7/5 by linarith)
          dsimp [b]
          rw [min_eq_right hL']
          dsimp [L]
          nlinarith
      have hh := mul_nonneg (show 0≤θ-1 by linarith) (show 0≤b-θ by linarith)
      have hval : θ*u/2+(L-θ)^2/4<2 := by
        rcases eq_or_lt_of_le hb1 with he | he
        · have hθ1 : θ=1 := by linarith
          rw [hθ1]
          exact hF1
        · have hgap : 0 < (b-θ)*(2-(1*u/2+(L-1)^2/4))+
                (θ-1)*(2-(b*u/2+(L-b)^2/4)) := by
            rcases eq_or_lt_of_le hb with hz | hz
            · rw [hz,sub_self,zero_mul,zero_add]
              exact mul_pos (by linarith) (by linarith)
            · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) (by linarith))
                (mul_nonneg (by linarith) (by linarith))
          have ha := mul_nonneg (show 0≤b-1 by linarith) hh
          have hprod : 0 < (b-1)*(2-(θ*u/2+(L-θ)^2/4)) := by
            linear_combination hgap + 1/4*ha
          by_contra! no
          have contra := mul_nonpos_of_nonneg_of_nonpos (show 0≤b-1 by linarith)
            (show 2-(θ*u/2+(L-θ)^2/4)≤0 by linarith)
          linarith
      have hm := min_le_right (u^2/4) (θ*u/2)
      change min (u^2/4) (θ*u/2)+(θ+(L-θ)^2/4)-θ<2
      linarith

variable {ι : Type*}

/-- Strict normalized one-heavy branch on a summable light bank. -/
theorem one_heavy_strict (p q : ι → ℝ) (P Q θ h : ℝ)
    (hθ : 1≤θ ∧ θ≤2) (hQ : 1<Q) (hqP : Q≤P) (_hP : P≤2)
    (hp : ∀ i, 0≤p i) (hq : ∀ i, 0≤q i ∧ q i≤1)
    (hs : Summable (fun i => p i+q i))
    (hmass : (∑' i, (p i+q i))+h+P+Q=6)
    (hnopivot : P+Q≤2+h) (hh : h<2) :
    Q*min θ P+(∑' i, q i*min θ (p i))-θ<2 := by
  have h2 : 2<P+Q := by linarith
  have h4 : P+Q<4 := by linarith
  have light := one_heavy_rebate p q θ (P+Q) hθ.1 h2.le h4.le hp hq hs (by linarith)
  have main := one_heavy_strict_scalar θ (P+Q) hθ.1 hθ.2 h2 h4
  have x : Q*min θ P≤(P+Q)^2/4 := by
    have m := mul_le_mul_of_nonneg_left (min_le_right θ P) (show 0≤Q by linarith)
    nlinarith [sq_nonneg (P-Q)]
  have y : Q*min θ P≤θ*(P+Q)/2 := by
    have m := mul_le_mul_of_nonneg_left (min_le_left θ P) (show 0≤Q by linarith)
    have m' := mul_le_mul_of_nonneg_left (show Q≤(P+Q)/2 by linarith)
      (show 0≤θ by linarith)
    nlinarith
  linarith [le_min x y]

#print axioms one_heavy_strict
end SparseHalfCountableEndpoint
