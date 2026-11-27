import LowSmallSide

namespace SparseHalfOutsideGreedy

noncomputable def prices (θ : ℝ) (bs : List (ℝ×ℝ)) : ℝ :=
  (bs.map fun b => b.2 * max 0 (θ-b.1)).sum

noncomputable def capacity (bs : List (ℝ×ℝ)) : ℝ := (bs.map Prod.snd).sum

noncomputable def cost : List (ℝ×ℝ) → ℝ → ℝ
  | [], _ => 0
  | b::bs, t => b.1 * min t b.2 + cost bs (max 0 (t-b.2))

theorem cost_zero (bs : List (ℝ×ℝ)) (hq : ∀ b ∈ bs, 0 ≤ b.2) :
    cost bs 0 = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := hq b (by simp)
    have ht := ih (fun x hx => hq x (by simp [hx]))
    simp [cost,min_eq_left hb,max_eq_left (neg_nonpos.mpr hb),ht]

/-- Ascending prices give the fractional fill optimum; the last used
price acts as a certificate for its value. -/
theorem cost_dual (bs : List (ℝ×ℝ)) (t : ℝ)
    (hq : ∀ b ∈ bs, 0 ≤ b.2)
    (hsort : bs.Pairwise (fun b c => b.1≤c.1))
    (ht : 0 < t) (hcap : t ≤ capacity bs) :
    ∃ b ∈ bs, cost bs t = b.1 * t - prices b.1 bs := by
  induction bs generalizing t with
  | nil => simp [capacity] at hcap; linarith
  | cons b bs ih =>
    obtain ⟨hord,hst⟩ := List.pairwise_cons.mp hsort
    have hb := hq b (by simp)
    have hqs : ∀ x ∈ bs, 0 ≤ x.2 := fun x hx => hq x (by simp [hx])
    by_cases hh : t≤b.2
    · have hzero : ∀ bs' : List (ℝ×ℝ), (∀ z ∈ bs', b.1≤z.1) → prices b.1 bs'=0 := by
        intro bs'
        induction bs' with
        | nil => simp [prices]
        | cons z zs ih =>
          intro horder
          have hz := horder z (by simp)
          have hh' := ih (fun v hv => horder v (by simp [hv]))
          simp only [prices,List.map_cons,List.sum_cons] at hh' ⊢
          rw [max_eq_left (sub_nonpos.mpr hz)]
          simpa using hh'
      refine ⟨b,by simp,?_⟩
      have hh' := hzero bs hord
      simp [cost, prices, min_eq_left hh, max_eq_left (sub_nonpos.mpr hh), cost_zero bs hqs, prices] at *
      linarith
    · have hp : 0<t-b.2 := by linarith
      have ht' : t-b.2 ≤ capacity bs := by
        simp only [capacity,List.map_cons,List.sum_cons] at hcap ⊢
        linarith
      obtain ⟨z,hz,he⟩ := ih (t-b.2) hqs hst hp ht'
      refine ⟨z,by simp [hz],?_⟩
      have horder := hord z hz
      rw [cost, min_eq_right (by linarith : b.2≤t), max_eq_right hp.le, he]
      simp only [prices,List.map_cons,List.sum_cons]
      rw [max_eq_right (sub_nonneg.mpr horder)]
      ring

/-- End-to-end inequality for the cheapest half wholly outside A.
Masses scaled by ten. This theorem covers outside capacity exactly six. -/
theorem cost_le_two (bs : List (ℝ×ℝ))
    (hps : ∀ b ∈ bs, 0 ≤ b.1 ∧ b.1≤2)
    (hqs : ∀ b ∈ bs, 0 ≤ b.2 ∧ b.2≤1 ∧ b.2≤b.1)
    (hsort : bs.Pairwise (fun b c => b.1≤c.1))
    (hB : (bs.map fun b => b.1+b.2).sum = 6)
    (ht : 0<5-(bs.map Prod.fst).sum) :
    cost bs (5-(bs.map Prod.fst).sum) ≤ 2 := by
  have hq : ∀ b ∈ bs, 0 ≤ b.2 := fun b hb => (hqs b hb).1
  have hm : ∀ x : List (ℝ×ℝ), (x.map fun b => b.1+b.2).sum =
      (x.map Prod.fst).sum + capacity x := by
    intro x
    induction x with
    | nil => simp [capacity]
    | cons z zs ih =>
      simp only [List.map_cons,List.sum_cons,capacity] at ih ⊢
      linarith
  have hc : 5-(bs.map Prod.fst).sum ≤ capacity bs := by linarith [hm bs]
  obtain ⟨z,hz,hval⟩ := cost_dual bs _ hq hsort ht hc
  rw [hval]
  let θ := z.1
  have hθ0 : 0≤θ := (hps z hz).1
  have hθ2 : θ≤2 := (hps z hz).2
  change θ * (5-(bs.map Prod.fst).sum) - prices θ bs ≤ 2
  by_cases hθ1 : θ≤1
  · have HP : ∀ x : List (ℝ×ℝ), (∀ b ∈ x, b.2≤b.1) →
        capacity x≤(x.map Prod.fst).sum := by
      intro x
      induction x with
      | nil => simp [capacity]
      | cons b bs ih =>
        intro hbd
        have h1 := ih (fun b hb => hbd b (by simp [hb]))
        have h2 := hbd b (by simp)
        simp only [List.map_cons,List.sum_cons,capacity] at h1 ⊢
        linarith
    have hle : 5-(bs.map Prod.fst).sum ≤ 2 := by
      linarith [hm bs, HP bs (fun b hb => (hqs b hb).2.2)]
    have hprices : ∀ x : List (ℝ×ℝ), (∀ b ∈ x, 0≤b.2) → 0≤prices θ x := by
      intro x
      induction x with
      | nil => simp [prices]
      | cons b bs ih =>
        intro hbd
        have h := ih (fun b hb => hbd b (by simp [hb]))
        exact add_nonneg (mul_nonneg (hbd b (by simp)) (le_max_left ..)) h
    have h1 := mul_le_mul hθ1 hle (le_of_lt ht) (show (0:ℝ)≤1 by norm_num)
    linarith [hprices bs hq]
  · have hdual := SparseHalfLowSmallSide.dual θ (by linarith) hθ2 bs
      (fun b hb => (hps b hb).1) (fun b hb => ⟨(hqs b hb).1,(hqs b hb).2.1⟩) hB
    have hs : ∀ x : List (ℝ×ℝ),
        (x.map fun b => b.2 * min θ b.1).sum + prices θ x = θ * capacity x := by
      intro x
      induction x with
      | nil => simp [prices,capacity]
      | cons b bs ih =>
        have he : min θ b.1 + max 0 (θ-b.1) = θ := by
          by_cases ht : θ≤b.1
          · rw [min_eq_left ht,max_eq_left (sub_nonpos.mpr ht),add_zero]
          · rw [min_eq_right (by linarith : b.1≤θ),max_eq_right (by linarith : 0≤θ-b.1)]
            ring
        have hprod := congrArg (fun x : ℝ => b.2*x) he
        simp only [List.map_cons,List.sum_cons,prices,capacity] at ih ⊢
        nlinarith
    have heq := hm bs
    rw [hB] at heq
    nlinarith [hs bs] 

#print axioms cost_le_two
end SparseHalfOutsideGreedy
