import OneHeavyNormalized

namespace SparseHalfOneHeavyPacking
open SparseHalfLowSmallSide SparseHalfConvexPacking

theorem g0 : g 0=0 := by rw [eq_small _ (by norm_num)]; norm_num

theorem lip {x y : ℝ} (hy : 0≤y) (hxy : x≤y) : g y≤g x+(y-x) := by
  have h0 : 0 ≤ c y := le_min (by norm_num) (by linarith)
  have h1 : c y ≤ 1 := min_le_left ..
  have h2 := ge_line x (c y) h0 h1
  have h3 := mul_le_mul_of_nonneg_right h1 (show 0≤y-x by linarith)
  change c y * (y-c y)≤g x+(y-x)
  nlinarith

theorem sum_le (xs : List ℝ) (hx : ∀ x ∈ xs, 0≤x) :
    (xs.map g).sum≤xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    have h1 := lip h h
    rw [g0] at h1
    simp only [List.map_cons,List.sum_cons]
    linarith

/-- Losing δ capacity in the list costs at most δ objective, uniformly
over the number of capped blocks. -/
theorem trim (xs : List ℝ) (L δ s : ℝ) (hL : 0≤L) (hδ : 0≤δ)
    (hx : ∀ x ∈ xs, 0≤x ∧ x≤s) (hcap : xs.sum≤L+δ) :
    ∃ ys : List ℝ, (∀ y ∈ ys, 0≤y ∧ y≤s) ∧ ys.sum≤L ∧
      (xs.map g).sum≤(ys.map g).sum+δ := by
  induction xs generalizing L with
  | nil =>
    exact ⟨[],by simp,by simpa using hL,by simpa using hδ⟩
  | cons x xs ih =>
    obtain ⟨hx0,hxs⟩ := hx x (by simp)
    have htail : ∀ z ∈ xs, 0≤z ∧ z≤s := fun z hz => hx z (by simp [hz])
    by_cases hh : x≤L
    · obtain ⟨ys,hy,hys,hval⟩ := ih (L-x) (by linarith) htail
        (by simp only [List.sum_cons] at hcap; linarith)
      refine ⟨x::ys, ?_, ?_, ?_⟩
      · intro y hm
        rcases List.mem_cons.mp hm with rfl | hd
        · exact ⟨hx0,hxs⟩
        · exact hy y hd
      · simp only [List.sum_cons]; linarith
      · simp only [List.map_cons,List.sum_cons]; linarith
    · have hsL : L≤s := by linarith
      have ho := lip hx0 (show L≤x by linarith)
      have ht := sum_le xs (fun z hz => (htail z hz).1)
      refine ⟨[L],by simpa using And.intro hL hsL,by simp,?_⟩
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hcap ⊢
      linarith

theorem packed_le (θ L : ℝ) (hθ : 1≤θ) (hL : 0≤L) (hL4 : L≤4)
    (xs : List ℝ) (hxs : ∀ x ∈ xs, 0≤x ∧ x≤θ+1) (hS : xs.sum≤L) :
    (xs.map g).sum≤ (if L≤θ+1 then g L else θ+g (L-(θ+1))) := by
  obtain ⟨k,r,hr,hrs,he,hb⟩ :=
    pack g (θ+1) (by linarith) g0 (isConvex _) xs hxs
  have hgs : g (θ+1)=θ := by rw [eq_large _ (by linarith)]; ring
  rw [hgs] at hb
  have hkt : (k:ℝ)*2≤k*(θ+1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hkR : (k:ℝ)≤2 := by linarith
  have hk : k≤2 := by exact_mod_cast hkR
  have hcases : k=0 ∨ k=1 ∨ k=2 := by omega
  by_cases hf : L≤θ+1
  · rw [if_pos hf]
    rcases hcases with rfl | rfl | rfl
    · simp at he hb
      exact hb.trans (monotone_nonneg hr (by linarith))
    · simp at he hb
      have hLr : L=θ+1 := by linarith
      have hz : r=0 := by linarith
      simpa [hLr, hz, g0, hgs] using hb
    · norm_num at he
      exfalso; linarith
  · rw [if_neg hf]
    have hval : 0≤g (L-(θ+1)) := ge_zero _ (by linarith)
    rcases hcases with rfl | rfl | rfl
    · simp at hb
      have hm := monotone_nonneg hr hrs
      rw [hgs] at hm
      linarith
    · simp at he hb
      have hm := monotone_nonneg hr (show r≤L-(θ+1) by linarith)
      linarith
    · norm_num at he hb
      have hf0 : θ=1 := by linarith
      have hL1 : L=4 := by linarith
      have hr1 : r=0 := by linarith
      have haux : L-(θ+1)=θ+1 := by linarith
      rw [haux,hgs]
      simpa [hr1,g0,two_mul] using hb

theorem one_large_others_small (θ t u : ℝ)
    (hθ : 1≤θ) (hθ' : θ≤2) (ht : 1≤t)
    (hu : 2≤u) (hu' : u≤4)
    (xs : List ℝ) (hxs : ∀ x ∈ xs, 0≤x ∧ x≤θ+1)
    (hS : xs.sum≤7+t-2*u) :
    min (u^2/4) (θ*u/2)+(xs.map g).sum-θ*t≤2 := by
  obtain ⟨ys,hy,hys,hval⟩ :=
    trim xs (8-2*u) (t-1) (θ+1) (by linarith) (by linarith) hxs (by linarith)
  have hg := packed_le θ (8-2*u) hθ (by linarith) (by linarith) ys hy hys
  have hbase : (ys.map g).sum≤SparseHalfOneHeavyNormalized.base θ u := by
    unfold SparseHalfOneHeavyNormalized.base
    by_cases hh : 8-2*u≤θ+1
    · simpa [hh] using hg
    · simp only [if_neg hh] at hg ⊢
      rw [show 8-2*u-(θ+1)=7-2*u-θ by ring] at hg
      exact hg
  have hm := SparseHalfOneHeavyNormalized.main θ u hθ hθ' hu hu'
  have he := mul_nonneg (show 0≤t-1 by linarith) (show 0≤θ-1 by linarith)
  nlinarith

/-- Numerical outside-half dual for one exceptional smaller side.
Each light block is (larger capacity, smaller capacity). -/
theorem outside_dual (a h p q θ : ℝ) (ha : a≤4) (hθ : 1≤θ) (hθ' : θ≤2)
    (hq : 1≤q) (hqp : q≤p) (hp : p≤2) (hnopivot : p+q≤2+h)
    (bs : List (ℝ×ℝ)) (hB : a+h+p+q+(bs.map fun b => b.1+b.2).sum=10)
    (hl : ∀ b ∈ bs, 0≤b.1 ∧ 0≤b.2 ∧ b.2≤1) :
    q*min θ p+(bs.map fun b => b.2*min θ b.1).sum-θ*(5-a)≤2 := by
  let xs := bs.map fun b => min (θ+1) (b.1+b.2)
  have hxs : ∀ x ∈ xs, 0≤x ∧ x≤θ+1 := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1,h2,_⟩ := hl z hz
    exact ⟨le_min (by linarith) (add_nonneg h1 h2),min_le_left ..⟩
  have hsum (zs : List (ℝ×ℝ)) :
      (zs.map fun b => min (θ+1) (b.1+b.2)).sum ≤ (zs.map fun b => b.1+b.2).sum := by
    induction zs with
    | nil => simp
    | cons z zs ih =>
      simp only [List.map_cons,List.sum_cons]
      linarith [min_le_right (θ+1) (z.1+z.2)]
  have ht : xs.sum≤7+(5-a)-2*(p+q) := by
    have hh := hsum bs
    change xs.sum≤_ at hh
    linarith
  have hbound := one_large_others_small θ (5-a) (p+q) hθ hθ'
    (by linarith) (by linarith) (by linarith) xs hxs ht
  have hlow (zs : List (ℝ×ℝ)) (hZ : ∀ b ∈ zs, 0≤b.1 ∧ 0≤b.2 ∧ b.2≤1) :
    (zs.map fun b => b.2*min θ b.1).sum ≤
      ((zs.map fun b => min (θ+1) (b.1+b.2)).map g).sum := by
    induction zs with
    | nil => simp
    | cons z zs ih =>
      obtain ⟨_,h2,h3⟩ := hZ z (by simp)
      have hg := block_rebate θ z.1 z.2 hθ h2 h3
      have he := ih (fun b hb => hZ b (by simp [hb]))
      simp only [List.map_cons,List.sum_cons]
      linarith
  have hsmall := hlow bs hl
  change _≤(xs.map g).sum at hsmall
  have hq0 : 0≤q := by linarith
  have hP := mul_le_mul_of_nonneg_left (min_le_right θ p) hq0
  have hT := mul_le_mul_of_nonneg_left (min_le_left θ p) hq0
  have hT' := mul_le_mul_of_nonneg_left (show q≤(p+q)/2 by linarith) (show 0≤θ by linarith)
  have hpivot : q*min θ p ≤ min ((p+q)^2/4) (θ*(p+q)/2) := by
    apply le_min
    · nlinarith [sq_nonneg (p-q)]
    · nlinarith
  linarith

#print axioms outside_dual

#print axioms one_large_others_small
end SparseHalfOneHeavyPacking
