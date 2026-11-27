import ConvexPacking

namespace SparseHalfLowSmallSide
open SparseHalfConvexPacking

noncomputable def c (m : ℝ) : ℝ := min 1 (m/2)
noncomputable def g (m : ℝ) : ℝ := c m * (m - c m)

theorem eq_small (m : ℝ) (h : m ≤ 2) : g m = m^2/4 := by
  unfold g c
  rw [min_eq_right (show m/2 ≤ 1 by linarith)]
  ring

theorem eq_large (m : ℝ) (h : 2 ≤ m) : g m = m-1 := by
  unfold g c
  rw [min_eq_left (show 1 ≤ m/2 by linarith)]
  ring

theorem ge_zero (m : ℝ) (_hm : 0 ≤ m) : 0 ≤ g m := by
  by_cases hv : m ≤ 2
  · rw [eq_small _ hv]
    positivity
  · rw [eq_large _ (by linarith)]
    linarith

theorem ge_line (m z : ℝ) (_hz0 : 0 ≤ z) (hz1 : z ≤ 1) : z*(m-z) ≤ g m := by
  by_cases h : m ≤ 2
  · rw [eq_small _ h]
    nlinarith [sq_nonneg (z-m/2)]
  · rw [eq_large _ (by linarith)]
    have h0 := mul_nonneg (show 0 ≤ 1-z by linarith) (show 0 ≤ m-1-z by linarith)
    linarith [show (1-z)*(m-1-z) = m-1-z*(m-z) by ring]

theorem monotone_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : g x ≤ g y := by
  have h0 : 0 ≤ c x := le_min (by norm_num) (by linarith)
  have h1 : c x ≤ 1 := min_le_left .. 
  have he := ge_line y (c x) h0 h1
  dsimp [g]
  calc
    c x * (x-c x) ≤ c x * (y-c x) := mul_le_mul_of_nonneg_left (by linarith) h0
    _ ≤ g y := he

theorem isConvex (s : ℝ) : IsConvex g s := by
  intro x hx y hy u v hu hv huv
  let z := c (u*x+v*y)
  have hz0 : 0 ≤ z := le_min (by norm_num) (by
    have h := add_nonneg (mul_nonneg hu hx.1) (mul_nonneg hv hy.1)
    linarith)
  have hz1 : z ≤ 1 := min_le_left ..
  have h1 := mul_le_mul_of_nonneg_left (ge_line x z hz0 hz1) hu
  have h2 := mul_le_mul_of_nonneg_left (ge_line y z hz0 hz1) hv
  change z * (u*x+v*y-z) ≤ u*g x+v*g y
  have he : z * (u*x+v*y-z) = u*(z*(x-z))+v*(z*(y-z)) := by
    linear_combination z^2 * huv
  rw [he]
  linarith

theorem block_rebate (θ p q : ℝ) (hθ : 1 ≤ θ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) :
    q * min θ p ≤ g (min (θ+1) (p+q)) := by
  by_cases h : p+q ≤ θ+1
  · rw [min_eq_right h]
    calc
      _ ≤ q*p := mul_le_mul_of_nonneg_left (min_le_right ..) hq0
      _ = q*((p+q)-q) := by ring
      _ ≤ _ := ge_line _ _ hq0 hq
  · rw [min_eq_left (by linarith : θ+1 ≤ p+q), eq_large _ (by linarith)]
    have h1 := mul_le_mul_of_nonneg_left (min_le_left θ p) hq0
    have h2 := mul_le_mul_of_nonneg_right hq (show 0 ≤ θ by linarith)
    linarith

theorem packed_bound (θ : ℝ) (hθ : 1 ≤ θ) (hθ' : θ ≤ 2) (ys : List ℝ)
    (hy : ∀ x ∈ ys, 0 ≤ x ∧ x ≤ θ+1) (hyS : ys.sum ≤ 6) :
    (ys.map g).sum ≤ 2*θ+(2-θ)^2 := by
  obtain ⟨k,r,hr0,hrs,hm,hc⟩ := pack g (θ+1) (by linarith)
    (by rw [eq_small _ (by norm_num)]; norm_num) (isConvex _) ys hy
  have hg := eq_large (θ+1) (by linarith)
  have h0 : g (θ+1)=θ := by linarith
  rw [h0] at hc
  have hrθ := monotone_nonneg hr0 hrs
  rw [h0] at hrθ
  have hkt : (k:ℝ)*2 ≤ k*(θ+1) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hkR : (k:ℝ) ≤ 3 := by linarith
  have hk : k ≤ 3 := by exact_mod_cast hkR
  have hcases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · norm_num at hc
    nlinarith [sq_nonneg (2-θ)]
  · norm_num at hc
    nlinarith [sq_nonneg (2-θ)]
  · norm_num at hc hm
    have hlim : r ≤ 4-2*θ := by linarith
    have hv := monotone_nonneg hr0 hlim
    rw [eq_small _ (by linarith : 4-2*θ ≤ 2)] at hv
    nlinarith
  · norm_num at hc hm
    have he : θ=1 := by linarith
    have he' : r=0 := by linarith
    rw [he', eq_small _ (by norm_num), he] at hc
    rw [he]
    norm_num at hc ⊢
    exact hc

/-- The linear-programming objective for filling a half in a union of
bicliques, at any relevant threshold 1≤θ≤2, is at most two in the scaling
where the total outside mass is six and every smaller side is at most one. -/
theorem dual (θ : ℝ) (hθ : 1 ≤ θ) (hθ' : θ ≤ 2) (bs : List (ℝ×ℝ))
    (hp : ∀ b ∈ bs, 0 ≤ b.1) (hq : ∀ b ∈ bs, 0 ≤ b.2 ∧ b.2 ≤ 1)
    (ht : (bs.map fun b => b.1+b.2).sum = 6) :
    -θ + (bs.map fun b => b.2 * min θ b.1).sum ≤ 2 := by
  let ys := bs.map fun b => min (θ+1) (b.1+b.2)
  have hy : ∀ x ∈ ys, 0 ≤ x ∧ x ≤ θ+1 := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    exact ⟨le_min (by linarith) (add_nonneg (hp b hb) (hq b hb).1), min_le_left ..⟩
  have ht0 : ∀ zs : List (ℝ×ℝ), ((zs.map fun b => min (θ+1) (b.1+b.2)).sum) ≤
      (zs.map fun b => b.1+b.2).sum := by
    intro zs
    induction zs with
    | nil => simp
    | cons z zs ih =>
      simp only [List.map_cons,List.sum_cons]
      linarith [min_le_right (θ+1) (z.1+z.2)]
  have ht1 : ys.sum ≤ 6 := (ht0 bs).trans_eq ht
  have hc := packed_bound θ hθ hθ' ys hy ht1
  have hcomp :
      ∀ zs : List (ℝ×ℝ), (∀ z ∈ zs, 0 ≤ z.2 ∧ z.2 ≤ 1) →
      (zs.map fun b => b.2*min θ b.1).sum ≤
        ((zs.map fun b => min (θ+1) (b.1+b.2)).map g).sum := by
    intro zs
    induction zs with
    | nil => simp
    | cons z zs ih =>
      intro hz
      have htail := ih (fun b hb => hz b (by simp [hb]))
      have hr := hz z (by simp)
      simp only [List.map_cons,List.sum_cons]
      linarith [block_rebate θ z.1 z.2 hθ hr.1 hr.2]
  have hb := (hcomp bs hq).trans hc
  have hh := mul_nonneg (show 0 ≤ θ-1 by linarith) (show 0 ≤ 2-θ by linarith)
  nlinarith

#print axioms dual
end SparseHalfLowSmallSide
