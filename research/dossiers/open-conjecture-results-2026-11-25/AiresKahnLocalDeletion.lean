import Mathlib
namespace AiresKahnLocal
def ratioNumerator (s : ℚ) : ℚ := 4*(2*s-1)^4*(2*s+1)^2
def ratioDenominator (s : ℚ) : ℚ := s^2*(4*s-3)*(4*s-1)^2*(4*s+1)
theorem ratio_decay (s : ℚ) (hs : 2 ≤ s) :
    0 < ratioDenominator s ∧ ratioNumerator s < ratioDenominator s := by
  have hs0 : 0 < s := by linarith
  have b : 0 < 4*s - 3 := by linarith
  have c : 0 < 4*s - 1 := by linarith
  have d : 0 < 4*s + 1 := by linarith
  constructor
  · unfold ratioDenominator
    positivity
  · have hp : 0 ≤ s^3 * (96*s-112) :=
      mul_nonneg (pow_nonneg hs0.le _) (by linarith)
    have hq : 0 ≤ 13*s^2 := mul_nonneg (by norm_num) (sq_nonneg s)
    calc
      ratioNumerator s < ratioNumerator s + (s^3*(96*s-112)+13*s^2+(16*s-4)) := by linarith
      _ = ratioDenominator s := by unfold ratioNumerator ratioDenominator; ring
theorem hypergeom_variance_bounds (s : ℚ) (hs : 2 ≤ s) :
    s/8 ≤ (2*s-1)^2 / (4*(4*s-3)) ∧
    (2*s-1)^2 / (4*(4*s-3)) ≤ s/4 := by
  have h : 0 < 4*(4*s-3) := by linarith
  constructor
  · apply (le_div_iff₀ h).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ s) (by linarith : 0 ≤ 4*s-5)]
  · apply (div_le_iff₀ h).2
    nlinarith
theorem conditional_mean_slope (s a b : ℚ)
    (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ s) :
    b-a ≤ (4*s*b/(s+b)-1) - (4*s*a/(s+a)-1) := by
  have hsa : 0 < s+a := by linarith
  have hsb : 0 < s+b := by linarith
  have hprod : 0 < (s+a)*(s+b) := mul_pos hsa hsb
  have hsa' : s+a ≤ 2*s := by linarith
  have hsb' : s+b ≤ 2*s := by linarith
  have hbnd : (s+a)*(s+b) ≤ 2*s*(2*s) :=
    mul_le_mul hsa' hsb' hsb.le (by linarith)
  have heq : (4*s*b/(s+b)-1) - (4*s*a/(s+a)-1) =
    (4*s^2*(b-a))/((s+a)*(s+b)) := by
      field_simp [hsa.ne', hsb.ne']
      ring
  rw [heq]
  apply (le_div_iff₀ hprod).2
  calc
    (b-a)*((s+a)*(s+b)) ≤ (b-a)*(2*s*(2*s)) :=
      mul_le_mul_of_nonneg_left hbnd (sub_nonneg.mpr hab)
    _ = _ := by ring
theorem conditional_mean_pairwise (s a b : ℚ)
    (hs : 0 < s) (ha : 0 ≤ a) (ha' : a ≤ s)
    (hb : 0 ≤ b) (hb' : b ≤ s) :
    (b-a)^2 ≤ ((4*s*b/(s+b)-1) - (4*s*a/(s+a)-1))^2 := by
  rcases le_total a b with h | h
  · have h' := conditional_mean_slope s a b hs ha h hb'
    have hnon : 0 ≤ b-a := sub_nonneg.mpr h
    nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤
      ((4*s*b/(s+b)-1) - (4*s*a/(s+a)-1))+(b-a) by linarith)]
  · have h' := conditional_mean_slope s b a hs hb h ha'
    have hnon : 0 ≤ a-b := sub_nonneg.mpr h
    nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤
      ((4*s*a/(s+a)-1) - (4*s*b/(s+b)-1))+(a-b) by linarith)]
end AiresKahnLocal
#print axioms AiresKahnLocal.ratio_decay
#print axioms AiresKahnLocal.hypergeom_variance_bounds
#print axioms AiresKahnLocal.conditional_mean_slope
#print axioms AiresKahnLocal.conditional_mean_pairwise
namespace AiresKahnLocal
def central (n : ℕ) : ℚ := ((2*n).choose n : ℕ)
theorem central_pos (n : ℕ) : 0 < central n := by
  unfold central
  exact_mod_cast (Nat.choose_pos (show n ≤ 2*n by omega))
theorem central_factorial (n : ℕ) :
    central n * (n.factorial : ℚ)^2 = ((2*n).factorial : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
  have hn : 2*n-n = n := by omega
  rw [hn] at h
  unfold central
  simpa only [pow_two, Nat.cast_mul, mul_assoc] using
    (congrArg (fun t : ℕ => (t : ℚ)) h)
theorem central_succ (n : ℕ) :
    central (n+1) * (↑n+1) = 2*(2*(n:ℚ)+1)*central n := by
  have h := central_factorial n
  have H := central_factorial (n+1)
  have hn : 2*(n+1) = (2*n+1)+1 := by omega
  rw [hn, Nat.factorial_succ (2*n+1), Nat.factorial_succ (2*n),
    Nat.factorial_succ n] at H
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at H
  rw [← h] at H
  have v : (0:ℚ) < (n.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos n
  have u : (0:ℚ) < (↑n+1) := by positivity
  apply mul_right_cancel₀ (mul_ne_zero u.ne' (pow_ne_zero 2 v.ne'))
  calc
    _ = central (n+1) * ((↑n+1) * ↑(n.factorial))^2 := by ring
    _ = (2 * ↑n + 1 + 1) * ((2 * ↑n + 1) *
          (central n * (↑(n.factorial))^2)) := H
    _ = _ := by ring
end AiresKahnLocal
#print axioms AiresKahnLocal.central_succ
namespace AiresKahnLocal
open Nat
theorem central_succ_div (n : ℕ) :
    central (n+1) = (2*(2*(n:ℚ)+1)*central n)/(↑n+1) := by
  have h : (0:ℚ) < ↑n+1 := by positivity
  exact (eq_div_iff h.ne').2 (central_succ n)
def absMoment (n : ℕ) : ℚ :=
  ((n:ℚ)+1)^2 * central (n+1)^2 / (4*(2*(n:ℚ)+1)*central (2*n+1))
def secondMoment (n : ℕ) : ℚ := (2*(n:ℚ)+1)^2 / (4*(4*(n:ℚ)+1))
theorem absMoment_pos (n : ℕ) : 0 < absMoment n := by
  unfold absMoment
  have a := central_pos (n+1)
  have b := central_pos (2*n+1)
  positivity
theorem secondMoment_pos (n : ℕ) : 0 < secondMoment n := by
  unfold secondMoment
  positivity
theorem absMoment_recurrence (n : ℕ) :
    absMoment (n+1) = absMoment n *
    (2*(2*(n:ℚ)+1)*(2*(n:ℚ)+3)^2/
       (((n:ℚ)+1)*(4*(n:ℚ)+3)*(4*(n:ℚ)+5))) := by
  unfold absMoment
  simp only [Nat.cast_add, Nat.cast_one]
  have h1 := central_succ_div (n+1)
  have h2 := central_succ_div (2*n+1)
  have h3 := central_succ_div (2*n+1+1)
  rw [show 2*(n+1)+1 = 2*n+1+1+1 by omega, h1,h3,h2]
  push_cast
  have hq : (0:ℚ) ≤ (n:ℚ) := by positivity
  have hc := (central_pos (2*n+1)).ne'
  have hp1 : (0:ℚ) < ↑n+1 := by linarith
  have hp2 : (0:ℚ) < ↑n+1+1 := by linarith
  have hp3 : (0:ℚ) < 2*↑n+1 := by linarith
  have hp4 : (0:ℚ) < 2*↑n+1+1 := by linarith
  have hp5 : (0:ℚ) < 2*↑n+1+1+1 := by linarith
  have hp6 : (0:ℚ) < 2*(2*↑n+1)+1 := by linarith
  have hp7 : (0:ℚ) < 2*(2*↑n+1+1)+1 := by linarith
  have hp8 : (0:ℚ) < 4*↑n+3 := by linarith
  have hp9 : (0:ℚ) < 4*↑n+5 := by linarith
  have hp10 : (0:ℚ) < 2*(↑n+1)+1 := by linarith
  field_simp [hc,hp1.ne',hp2.ne',hp3.ne',hp4.ne',hp5.ne',hp6.ne',hp7.ne',hp8.ne',hp9.ne',hp10.ne']
  ring
end AiresKahnLocal
#print axioms AiresKahnLocal.absMoment_recurrence
namespace AiresKahnLocal
def momentRatio (n : ℕ) : ℚ := (absMoment n)^2 / secondMoment n
theorem momentRatio_succ (n : ℕ) :
    momentRatio (n+1) = momentRatio n *
      (ratioNumerator ((n:ℚ)+1)/ratioDenominator ((n:ℚ)+1)) := by
  unfold momentRatio
  rw [absMoment_recurrence]
  unfold secondMoment ratioNumerator ratioDenominator
  push_cast
  have hn : 0 ≤ (n:ℚ) := by positivity
  have a : (0:ℚ) < ↑n+1 := by linarith
  have b : (0:ℚ) < 2*↑n+1 := by linarith
  have c : (0:ℚ) < 2*↑n+3 := by linarith
  have d : (0:ℚ) < 4*↑n+1 := by linarith
  have e : (0:ℚ) < 4*↑n+3 := by linarith
  have f : (0:ℚ) < 4*↑n+5 := by linarith
  have b' : (0:ℚ) < 2*(↑n+1)+1 := by linarith
  have d' : (0:ℚ) < 4*(↑n+1)-3 := by linarith
  have e' : (0:ℚ) < 4*(↑n+1)-1 := by linarith
  have f' : (0:ℚ) < 4*(↑n+1)+1 := by linarith
  rw [show (4:ℚ)*(↑n+1)-3 = 4*↑n+1 by ring,
      show (4:ℚ)*(↑n+1)-1 = 4*↑n+3 by ring,
      show (4:ℚ)*(↑n+1)+1 = 4*↑n+5 by ring,
      show (2:ℚ)*(↑n+1)+1 = 2*↑n+3 by ring]
  field_simp [a.ne',b.ne',c.ne',d.ne',e.ne',f.ne']
  ring
theorem momentRatio_le (n : ℕ) (h : 1 ≤ n) :
    momentRatio n ≤ 4/5 := by
  induction n, h using Nat.le_induction with
  | base => norm_num [momentRatio, absMoment, secondMoment, central, Nat.choose]
  | succ n hn ih =>
    rw [momentRatio_succ]
    have hn' : (1:ℚ) ≤ ↑n := by exact_mod_cast hn
    have H := ratio_decay ((n:ℚ)+1) (by linarith)
    have hrat : ratioNumerator ((n:ℚ)+1)/ratioDenominator ((n:ℚ)+1) ≤ 1 :=
      (div_le_iff₀ H.1).2 (by simpa using H.2.le)
    have hpos : 0 ≤ momentRatio n :=
      div_nonneg (sq_nonneg _) (secondMoment_pos n).le
    calc
      _ ≤ momentRatio n * 1 := mul_le_mul_of_nonneg_left hrat hpos
      _ ≤ 4/5 := by simpa using ih
end AiresKahnLocal
#print axioms AiresKahnLocal.momentRatio_le
namespace AiresKahnLocal
theorem foldedVar_lower (n : ℕ) (hn : 1 ≤ n) :
    ((n:ℚ)+1)/40 ≤ secondMoment n - (absMoment n)^2 := by
  have hn' : (1:ℚ) ≤ ↑n := by exact_mod_cast hn
  have h := (hypergeom_variance_bounds ((n:ℚ)+1) (by linarith)).1
  have H : ((n:ℚ)+1)/8 ≤ secondMoment n := by
    convert h using 1
    unfold secondMoment
    ring_nf
  have L := momentRatio_le n hn
  unfold momentRatio at L
  have L' := (div_le_iff₀ (secondMoment_pos n)).1 L
  linarith
theorem shift_diverges_bound (h v k : ℚ) (hh : 0 < h) (hk : 0 < k)
    (hv : (4*h^2)/40 ≤ v) (hK : k ≤ 8*h) :
    1 + h/320 ≤ 1 + v/(4*k) := by
  apply add_le_add_right
  apply (le_div_iff₀ (by positivity : 0 < 4*k)).2
  have hnon : 0 ≤ h/80 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hK hnon
  nlinarith
end AiresKahnLocal
#print axioms AiresKahnLocal.foldedVar_lower
#print axioms AiresKahnLocal.shift_diverges_bound
namespace AiresKahnLocal
open scoped BigOperators
def chooseWeight (m t : ℕ) : ℚ := (m.choose t : ℚ)^2
def weightedBoundary (m t : ℕ) : ℚ := (t:ℚ)^2 * chooseWeight m t
theorem weightedBoundary_succ (m t : ℕ) (ht : t ≤ m) :
    weightedBoundary m (t+1) = ((m:ℚ)-t)^2 * chooseWeight m t := by
  have h := congrArg (fun a : ℕ => (a : ℚ)) (Nat.choose_succ_right_eq m t)
  push_cast [Nat.cast_sub ht] at h
  unfold weightedBoundary chooseWeight
  push_cast
  calc
    _ = (((m.choose (t+1) : ℚ) * ((t:ℚ)+1)))^2 := by ring
    _ = _ := by rw [h]; ring
theorem weightedBoundary_diff (m t : ℕ) (ht : t ≤ m) :
    (2*(t:ℚ)-m)*(m:ℚ)*chooseWeight m t =
     weightedBoundary m t - weightedBoundary m (t+1) := by
  rw [weightedBoundary_succ m t ht]
  unfold weightedBoundary
  ring
theorem telescoping_range (f : ℕ → ℚ) (a n : ℕ) :
    (∑ t ∈ Finset.range n, (f (a+t) - f (a+t+1))) =
      f a - f (a+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show a+n.succ = a+n+1 by omega]
    ring
theorem first_abs_half (n : ℕ) :
    (∑ t ∈ Finset.range (n+1),
      (2*((n+1+t:ℕ):ℚ) - (2*n+1:ℕ)) *
        chooseWeight (2*n+1) (n+1+t)) * (2*n+1:ℕ) =
      weightedBoundary (2*n+1) (n+1) := by
  rw [Finset.sum_mul]
  have h : ∀ t ∈ Finset.range (n+1),
      (2*((n+1+t:ℕ):ℚ) - (2*n+1:ℕ)) *
        chooseWeight (2*n+1) (n+1+t) * (2*n+1:ℕ) =
      weightedBoundary (2*n+1) (n+1+t) -
        weightedBoundary (2*n+1) (n+1+t+1) := by
    intro t ht
    have ht' := Finset.mem_range.1 ht
    rw [← weightedBoundary_diff (2*n+1) (n+1+t) (by omega)]
    ring
  rw [Finset.sum_congr rfl h, telescoping_range]
  have hzero : weightedBoundary (2*n+1) (n+1+(n+1)) = 0 := by
    unfold weightedBoundary chooseWeight
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num
  rw [hzero, sub_zero]
end AiresKahnLocal
#print axioms AiresKahnLocal.first_abs_half
namespace AiresKahnLocal
open scoped BigOperators
theorem weighted_binom (m k : ℕ) (hk : k ≤ m) :
    (∑ t ∈ Finset.range (m+1), m.choose t * m.choose t * t.choose k) =
      m.choose k * (2*m-k).choose (m-k) := by
  have hv := Nat.add_choose_eq (m-k) m (m-k)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (m-k).choose i * m.choose j)] at hv
  rw [show m+1 = k + ((m-k)+1) by omega, Finset.sum_range_add]
  have hzero : (∑ t ∈ Finset.range k, m.choose t*m.choose t*t.choose k) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 ht), Nat.mul_zero]
  rw [hzero, zero_add, show 2*m-k = (m-k)+m by omega, hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.1 ht
  have hm : k+t ≤ m := by omega
  have H := Nat.choose_mul (n:=m) (k:=k+t) (s:=k) (by omega)
  rw [show k+t-k = t by omega] at H
  nth_rw 2 [← Nat.choose_symm hm]
  rw [show m-(k+t) = m-k-t by omega]
  calc
    _ = (m.choose (k+t)*(k+t).choose k) * m.choose (m-k-t) := by ac_rfl
    _ = _ := by rw [H]; ac_rfl
theorem weighted_binom_product (m k : ℕ) (hk : k ≤ m) :
    ((∑ t ∈ Finset.range (m+1), m.choose t * m.choose t * t.choose k) *
      (2*m).choose k) =
      (m.choose k)^2 * (2*m).choose m := by
  rw [weighted_binom m k hk]
  have H := Nat.choose_mul (n:=2*m) (k:=m) (s:=k) hk
  calc
    _ = m.choose k * ((2*m).choose k * (2*m-k).choose (m-k)) := by ac_rfl
    _ = _ := by rw [← H]; ring
end AiresKahnLocal
#print axioms AiresKahnLocal.weighted_binom
#print axioms AiresKahnLocal.weighted_binom_product
namespace AiresKahnLocal
open scoped BigOperators
def binomMoment (m k : ℕ) : ℚ :=
  (∑ t ∈ Finset.range (m+1), chooseWeight m t * (t.choose k : ℚ)) / central m
theorem binomMoment_eq (m k : ℕ) (hk : k ≤ m) :
    binomMoment m k = ((m.choose k:ℚ)^2)/((2*m).choose k:ℚ) := by
  have h := congrArg (fun x : ℕ => (x : ℚ)) (weighted_binom_product m k hk)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sum] at h
  unfold binomMoment
  have Hm := (central_pos m).ne'
  have Hk : ((2*m).choose k:ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show k ≤ 2*m by omega)).ne'
  apply (div_eq_div_iff Hm Hk).2
  simpa [chooseWeight, pow_two, central] using h
theorem choose_two_cast (m : ℕ) :
    2*(m.choose 2 : ℚ) = (m:ℚ)*((m:ℚ)-1) := by
  by_cases hm : 1 ≤ m
  · have h := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))
    rw [← Nat.choose_two_right] at h
    have H := congrArg (fun x : ℕ => (x:ℚ)) h
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hm,Nat.cast_one] at H
    linarith
  · have hz : m=0 := by omega
    subst m
    norm_num [Nat.choose]
theorem second_overall (m : ℕ) (hm : 2 ≤ m) :
    (∑ t ∈ Finset.range (m+1), chooseWeight m t * ((t:ℚ)-(m:ℚ)/2)^2)
       / central m = (m:ℚ)^2/(4*(2*(m:ℚ)-1)) := by
  have hn : (2:ℚ) ≤ ↑m := by exact_mod_cast hm
  have hp : 0 < (m:ℚ) := by linarith
  have hp' : 0 < 2*(m:ℚ)-1 := by linarith
  have h0 := binomMoment_eq m 0 (by omega)
  have h1 := binomMoment_eq m 1 (by omega)
  have h2 := binomMoment_eq m 2 hm
  simp only [Nat.choose_zero_right,Nat.cast_one,one_pow,div_one] at h0
  simp only [Nat.choose_one_right,Nat.cast_mul,Nat.cast_ofNat] at h1
  have C := choose_two_cast m
  have D := choose_two_cast (2*m)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at D
  have C' : (m.choose 2:ℚ) = (m:ℚ)*((m:ℚ)-1)/2 := by linarith
  have D' : ((2*m).choose 2:ℚ) = (2*(m:ℚ))*(2*(m:ℚ)-1)/2 := by linarith
  rw [C',D'] at h2
  calc
    _ = 2*binomMoment m 2 + (1-(m:ℚ))*binomMoment m 1 +
        ((m:ℚ)^2/4)*binomMoment m 0 := by
      unfold binomMoment
      simp only [← mul_div_assoc, Finset.mul_sum, ← add_div, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, mul_one]
      have ht := choose_two_cast t
      linear_combination -chooseWeight m t * ht
    _ = _ := by
      rw [h0,h1,h2]
      field_simp [hp.ne',hp'.ne']
      ring
end AiresKahnLocal
#print axioms AiresKahnLocal.second_overall
namespace AiresKahnLocal
open scoped BigOperators
theorem half_reflection (n : ℕ) (f : ℕ → ℚ)
    (hf : ∀ t < n+1, f t = f (2*n+1-t)) :
    (∑ t ∈ Finset.range (2*n+2), f t) =
      2*(∑ t ∈ Finset.range (n+1), f (n+1+t)) := by
  rw [show 2*n+2 = (n+1)+(n+1) by omega, Finset.sum_range_add]
  have H : (∑ t ∈ Finset.range (n+1), f t) =
      ∑ t ∈ Finset.range (n+1), f (n+1+t) := by
    rw [← Finset.sum_range_reflect f (n+1)]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.1 ht
    rw [hf _ (by omega)]
    congr 1
    omega
  rw [H]
  ring
theorem chooseWeight_reflect (m t : ℕ) (ht : t ≤ m) :
    chooseWeight m (m-t) = chooseWeight m t := by
  unfold chooseWeight
  rw [Nat.choose_symm ht]
theorem mass_half (n : ℕ) :
    (∑ t ∈ Finset.range (n+1), chooseWeight (2*n+1) (n+1+t)) =
      central (2*n+1)/2 := by
  have h := binomMoment_eq (2*n+1) 0 (by omega)
  simp only [binomMoment,Nat.choose_zero_right,Nat.cast_one,one_pow,
    div_one,mul_one,show 2*n+1+1 = 2*n+2 by omega] at h
  rw [half_reflection n (chooseWeight (2*n+1))
      (fun t ht => (chooseWeight_reflect _ _ (by omega)).symm)] at h
  have H := (div_eq_iff (central_pos (2*n+1)).ne').1 h
  linarith
theorem half_centered_second (n : ℕ) (hn : 1 ≤ n) :
    (∑ t ∈ Finset.range (n+1), chooseWeight (2*n+1) (n+1+t) *
      (((n+1+t:ℕ):ℚ)-((2*n+1:ℕ):ℚ)/2)^2) /
    (∑ t ∈ Finset.range (n+1), chooseWeight (2*n+1) (n+1+t)) =
    secondMoment n := by
  have h := second_overall (2*n+1) (by omega)
  rw [show 2*n+1+1 = 2*n+2 by omega] at h
  rw [half_reflection n (fun t =>
      chooseWeight (2*n+1) t * ((t:ℚ)-((2*n+1:ℕ):ℚ)/2)^2)] at h
  · rw [mass_half]
    unfold secondMoment
    push_cast at *
    convert h using 1 <;> ring
  · intro t ht
    rw [chooseWeight_reflect _ _ (by omega), Nat.cast_sub (show t ≤ 2*n+1 by omega)]
    ring
theorem central_half (n : ℕ) :
    ((2*n+1).choose (n+1):ℚ) = central (n+1)/2 := by
  have h := Nat.choose_succ_succ (2*n+1) n
  have H : (2*n+1).choose n = (2*n+1).choose (n+1) := by
    rw [show 2*n+1=n+(n+1) by omega]
    exact Nat.choose_symm_add
  rw [H] at h
  have J := congrArg (fun t : ℕ => (t:ℚ)) h
  unfold central
  rw [show 2*(n+1) = (2*n+1).succ by omega]
  push_cast at J
  linarith
theorem half_centered_first (n : ℕ) :
    (∑ t ∈ Finset.range (n+1), chooseWeight (2*n+1) (n+1+t) *
      (((n+1+t:ℕ):ℚ)-((2*n+1:ℕ):ℚ)/2)) /
    (∑ t ∈ Finset.range (n+1), chooseWeight (2*n+1) (n+1+t)) =
    absMoment n := by
  have h := first_abs_half n
  have H : (2:ℚ)*(∑ t ∈ Finset.range (n+1), chooseWeight (2*n+1) (n+1+t) *
      (((n+1+t:ℕ):ℚ)-((2*n+1:ℕ):ℚ)/2)) * ((2*n+1:ℕ):ℚ)
      = weightedBoundary (2*n+1) (n+1) := by
    rw [Finset.mul_sum]
    convert h using 1
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [mass_half]
  unfold absMoment
  have W : weightedBoundary (2*n+1) (n+1) =
    ((n:ℚ)+1)^2 * (central (n+1)/2)^2 := by
      unfold weightedBoundary chooseWeight
      rw [central_half]
      push_cast
      rfl
  rw [W] at H
  push_cast at H ⊢
  generalize hsum : (∑ t ∈ Finset.range (n+1), chooseWeight (2*n+1) (n+1+t) *
      (((n:ℚ)+1+(t:ℚ))-(2*(n:ℚ)+1)/2)) = S at H ⊢
  have A : (0:ℚ) ≤ ↑n := by positivity
  have B : (0:ℚ) < 2*↑n+1 := by linarith
  field_simp [(central_pos (2*n+1)).ne',B.ne']
  linear_combination 4*H
end AiresKahnLocal
#print axioms AiresKahnLocal.half_centered_second
#print axioms AiresKahnLocal.half_centered_first
namespace AiresKahnLocal
open scoped BigOperators
section Weighted
variable {ι : Type} [Fintype ι]
def wmean (w f : ι → ℚ) : ℚ := ∑ i, w i*f i
def wvar (w f : ι → ℚ) : ℚ := wmean w (fun i => f i^2) - (wmean w f)^2
theorem wmean_const (w : ι → ℚ) (hw : ∑ i, w i=1) (c : ℚ) :
    wmean w (fun _ => c) = c := by
  unfold wmean
  rw [← Finset.sum_mul, hw, one_mul]
theorem wmean_add (w f g : ι → ℚ) :
    wmean w (fun i => f i+g i) = wmean w f+wmean w g := by
  unfold wmean
  simp_rw [mul_add, Finset.sum_add_distrib]
theorem wmean_mul (w f : ι → ℚ) (c : ℚ) :
    wmean w (fun i => c*f i) = c*wmean w f := by
  unfold wmean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem wmean_sub (w f g : ι → ℚ) :
    wmean w (fun i => f i-g i) = wmean w f-wmean w g := by
  unfold wmean
  simp_rw [mul_sub, Finset.sum_sub_distrib]
theorem wmean_mono (w f g : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (h : ∀ i, f i ≤ g i) : wmean w f ≤ wmean w g := by
  unfold wmean
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i))
theorem wvar_centered (w f : ι → ℚ) (hw : ∑ i, w i=1) :
    wvar w f = wmean w (fun i => (f i-wmean w f)^2) := by
  let a := wmean w f
  change wmean w (fun i => f i^2)-a^2 = wmean w (fun i => (f i-a)^2)
  have H : (fun i => (f i-a)^2) = fun i => (f i^2 - (2*a)*f i)+a^2 := by
    funext i
    ring
  rw [H,wmean_add,wmean_sub,wmean_mul,wmean_const w hw]
  change _ = _ - (2*a)*a + a^2
  ring
theorem pair_inner (w f : ι → ℚ) (hw : ∑ i, w i=1) (a : ℚ) :
    wmean w (fun j => (a-f j)^2) =
      a^2 - 2*a*wmean w f + wmean w (fun j => f j^2) := by
  have H : (fun j => (a-f j)^2) = fun j => (a^2 - (2*a)*f j)+ f j^2 := by
    funext j
    ring
  rw [H,wmean_add,wmean_sub,wmean_mul,wmean_const w hw]
theorem wvar_pairwise (w f : ι → ℚ) (hw : ∑ i, w i=1) :
    2*wvar w f = wmean w (fun i => wmean w (fun j => (f i-f j)^2)) := by
  simp_rw [pair_inner w f hw]
  rw [wmean_add,wmean_sub,
    show (fun i => 2*f i*wmean w f) = (fun i => (2*wmean w f)*f i) by
      funext i
      ring,
    wmean_mul,wmean_const w hw]
  unfold wvar
  ring
theorem wvar_compare (w f g : ι → ℚ) (hw : ∑ i,w i=1) (hw' : ∀ i,0 ≤ w i)
    (H : ∀ i j, (f i-f j)^2 ≤ (g i-g j)^2) :
    wvar w f ≤ wvar w g := by
  have h : wmean w (fun i => wmean w (fun j => (f i-f j)^2))
       ≤ wmean w (fun i => wmean w (fun j => (g i-g j)^2)) :=
    wmean_mono _ _ _ hw' (fun i => wmean_mono _ _ _ hw' (H i))
  rw [← wvar_pairwise w f hw, ← wvar_pairwise w g hw] at h
  linarith
theorem wvar_nonneg (w f : ι → ℚ) (hw : ∑ i,w i=1) (hw' : ∀ i,0 ≤ w i) :
    0 ≤ wvar w f := by
  rw [wvar_centered w f hw]
  unfold wmean
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw' i) (sq_nonneg _))
end Weighted
end AiresKahnLocal
#print axioms AiresKahnLocal.wvar_compare
namespace AiresKahnLocal
open scoped BigOperators
section Grouped
variable {ι : Type} [Fintype ι] {β : ι → Type} [∀ i, Fintype (β i)]
def joint (w : ι → ℚ) (u : ∀ i, β i → ℚ) : Sigma β → ℚ :=
  fun x => w x.1 * u x.1 x.2
theorem wmean_joint (w : ι → ℚ) (u : ∀ i, β i → ℚ) (f : Sigma β → ℚ) :
    wmean (joint w u) f = wmean w (fun i => wmean (u i) (fun j => f ⟨i,j⟩)) := by
  unfold wmean
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [joint,mul_assoc]
theorem var_total_ge (w : ι → ℚ) (u : ∀ i, β i → ℚ) (f : Sigma β → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, ∑ j, u i j=1) (hp : ∀ i j, 0 ≤ u i j) :
    wvar w (fun i => wmean (u i) (fun j => f ⟨i,j⟩)) ≤ wvar (joint w u) f := by
  unfold wvar
  rw [wmean_joint,wmean_joint]
  apply sub_le_sub_right
  apply wmean_mono _ _ _ hw
  intro i
  have H := wvar_nonneg (u i) (fun j => f ⟨i,j⟩) (hu i) (hp i)
  unfold wvar at H
  linarith
end Grouped
section Reflection
variable {ι : Type} [Fintype ι]
theorem wmean_invariant (w f : ι → ℚ) (e : ι ≃ ι)
    (hw : ∀ i, w (e i) = w i) : wmean w (fun i => f (e i)) = wmean w f := by
  unfold wmean
  apply Fintype.sum_equiv e
  intro i
  rw [hw]
def covar (w f g : ι → ℚ) : ℚ := wmean w (fun i=>f i*g i) - wmean w f * wmean w g
theorem covariance_reflected (w sum gap : ι → ℚ) (center : ℚ) (e : ι ≃ ι)
    (hw : ∑ i,w i=1) (hw' : ∀ i,w (e i)=w i)
    (he : ∀ i,sum (e i)=2*center-sum i) (hg : ∀ i,gap (e i)=gap i) :
    covar w sum gap = 0 := by
  have H := wmean_invariant w sum e hw'
  simp_rw [he] at H
  rw [wmean_sub,wmean_const w hw] at H
  have G := wmean_invariant w (fun i => sum i*gap i) e hw'
  simp_rw [he,hg,sub_mul] at G
  rw [wmean_sub,wmean_mul] at G
  unfold covar
  have hs : wmean w sum = center := by linarith
  rw [hs]
  linarith
theorem covariance_rank (w p q k : ι → ℚ)
    (hK : ∀ i,k i=q i-p i) (h0 : covar w (fun i=>p i+q i) k=0) :
    covar w q k = wvar w k/2 := by
  have h : q = fun i=>((p i+q i)+k i)/2 := by
    funext i
    rw [hK]
    ring
  have h' : (fun i=>q i*k i) = fun i=>(1/2:ℚ)*((p i+q i)*k i+k i^2) := by
    funext i
    rw [hK]
    ring
  have hq : wmean w q = (wmean w (fun i=>p i+q i) + wmean w k)/2 := by
    conv_lhs => rw [h]
    simp only [div_eq_mul_inv, mul_comm _ ((2:ℚ)⁻¹)]
    rw [wmean_mul,wmean_add]
  unfold covar at h0 ⊢
  unfold wvar
  rw [h',wmean_mul,wmean_add,hq]
  linear_combination h0/2
end Reflection
end AiresKahnLocal
#print axioms AiresKahnLocal.var_total_ge
#print axioms AiresKahnLocal.covariance_rank
namespace AiresKahnLocal
open scoped BigOperators
theorem hockey_range (n a : ℕ) :
    (∑ p ∈ Finset.range (n+1), p.choose a) = (n+1).choose (a+1) := by
  induction n with
  | zero =>
    cases a <;> simp [Nat.choose]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    rw [Nat.add_comm]
    exact (Nat.choose_succ_succ (n+1) a).symm
theorem rankWeight_mass (n a b : ℕ) :
  (∑ p ∈ Finset.range (n+1), p.choose a * (n-p).choose b) =
    (n+1).choose (a+b+1) := by
  induction n generalizing a b with
  | zero =>
    cases a <;> cases b <;> simp [Nat.choose]
  | succ n ih =>
    cases b with
    | zero => simpa using hockey_range (n+1) a
    | succ b =>
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self,Nat.choose_zero_succ,mul_zero,add_zero]
      have h : ∀ p ∈ Finset.range (n+1),
          p.choose a * (n.succ-p).choose (b+1) =
          p.choose a*(n-p).choose b+p.choose a*(n-p).choose (b+1) := by
        intro p hp
        rw [Nat.succ_sub (show p≤n from Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)),
          Nat.choose_succ_succ,Nat.mul_add]
      rw [Finset.sum_congr rfl h,Finset.sum_add_distrib,ih,ih]
      exact (Nat.choose_succ_succ (n+1) (a+b+1)).symm
theorem rankWeight_mul (p a : ℕ) :
    (p+1)*p.choose a = (a+1)*(p+1).choose (a+1) := by
  have h := Nat.choose_mul (n:=p+1) (k:=a+1) (s:=1) (by omega)
  simp only [Nat.choose_one_right, Nat.add_sub_cancel] at h
  rw [Nat.mul_comm] at h
  exact h.symm
theorem rankWeight_total (n a b : ℕ) :
  (∑ p ∈ Finset.range (n+1), (p+1)*p.choose a * (n-p).choose b) =
    (a+1)*(n+2).choose (a+b+2) := by
  simp only [rankWeight_mul,mul_assoc,←Finset.mul_sum]
  have H := rankWeight_mass (n+1) (a+1) b
  rw [Finset.sum_range_succ'] at H
  simp only [Nat.choose_zero_succ,zero_mul,add_zero] at H
  have hh : ∀ p ∈ Finset.range (n+1),
      (p+1).choose (a+1)*(n+1-(p+1)).choose b =
      (p+1).choose (a+1)*(n-p).choose b := by intro p _; congr 2; omega
  rw [Finset.sum_congr rfl hh] at H
  rw [H]
  congr 2
  omega
end AiresKahnLocal
#print axioms AiresKahnLocal.rankWeight_total
namespace AiresKahnSubset
def indexedRank (p : Finset Nat) {k : Nat} (h : p.card=k) (i : Fin k) :=
  (p.orderIsoOfFin h i).val

theorem indexedRank_mono (p : Finset Nat) {k : Nat} (h : p.card=k) :
    StrictMono (indexedRank p h) :=
  fun _ _ hi => (p.orderIsoOfFin h).strictMono hi

theorem indexedRank_mem (p : Finset Nat) {k : Nat} (h : p.card=k) (i : Fin k) :
    indexedRank p h i∈p := (p.orderIsoOfFin h i).property

theorem indexedRank_before (p : Finset Nat) {k : Nat} (h : p.card=k) (i : Fin k) (l : Nat) :
    indexedRank p h i < l ↔ i.val < (p.filter (·<l)).card := by
  classical
  let e := p.orderIsoOfFin h
  let F := p.filter (·<l)
  change indexedRank p h i < l ↔ i.val < F.card
  constructor
  · intro hi
    let f (j : Nat) := if hj : j<k then indexedRank p h ⟨j,hj⟩ else 0
    have hf := Finset.card_le_card_of_injOn f (s:=Finset.range (i.val+1)) (t:=F)
      (by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hk : j<k := by have ht := i.isLt; omega
        simp only [f,dite_eq_left hk]
        have hle : (⟨j,hk⟩ : Fin k) ≤ i := by exact Nat.le_of_lt_succ hj'
        exact Finset.mem_filter.mpr ⟨indexedRank_mem .., ((indexedRank_mono p h).monotone hle).trans_lt hi⟩)
      (by
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp ha
        have hb' := Finset.mem_range.mp hb
        have haK : a<k := by have hi := i.isLt; omega
        have hbK : b<k := by have hi := i.isLt; omega
        simp only [f,dite_eq_left haK,dite_eq_left hbK] at hab
        exact congrArg Fin.val ((indexedRank_mono p h).injective hab))
    rw [Finset.card_range] at hf
    omega
  · intro hc
    by_contra! hi
    let f (x : Nat) := if hx : x∈p then (e.symm ⟨x,hx⟩).val else 0
    have hf := Finset.card_le_card_of_injOn f (s:=F) (t:=Finset.range i.val)
      (by
        intro x hx
        have ⟨hm,hx'⟩ := Finset.mem_filter.mp hx
        have hxi : (e.symm ⟨x,hm⟩) < i := by
          by_contra! hh
          have hle := (indexedRank_mono p h).monotone hh
          have heq : indexedRank p h (e.symm ⟨x,hm⟩)=x := by
            change (e (e.symm ⟨x,hm⟩)).val=x
            simp
          omega
        exact Finset.mem_range.mpr (by simpa only [f,dite_eq_left hm,Fin.lt_def] using hxi))
      (by
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).1
        have hb' := (Finset.mem_filter.mp hb).1
        simp only [f,dite_eq_left ha',dite_eq_left hb'] at hab
        have hx := e.symm.injective (Fin.ext hab)
        exact congrArg Subtype.val hx)
    rw [Finset.card_range] at hf
    omega

end AiresKahnSubset
namespace AiresKahnSubset
open scoped BigOperators
abbrev Sel (B : Finset ℕ) (k : ℕ) := ↥(B.powersetCard k)
theorem selCard {B : Finset ℕ} {k : ℕ} (p : Sel B k) : p.val.card=k :=
  (Finset.mem_powersetCard.mp p.property).2
def srank {B : Finset ℕ} {k : ℕ} (p : Sel B k) (j : Fin k) : ℕ :=
  indexedRank p.val (selCard p) j
def before (p : Finset ℕ) (x : ℕ) := p.filter (·<x)
def after (p : Finset ℕ) (x : ℕ) := p.filter (x<·)
theorem before_after (p : Finset ℕ) (x : ℕ) :
    before p x ∪ after p x = p.erase x := by
  ext a
  simp only [before,after,Finset.mem_union,Finset.mem_filter,Finset.mem_erase]
  constructor
  · rintro (⟨h,q⟩|⟨h,q⟩)
    · exact ⟨by omega,h⟩
    · exact ⟨by omega,h⟩
  · rintro ⟨hx,h⟩
    rcases lt_or_gt_of_ne hx with q|q
    · exact Or.inl ⟨h,q⟩
    · exact Or.inr ⟨h,q⟩
theorem before_after_disjoint (p q : Finset ℕ) (x : ℕ) :
    Disjoint (before p x) (after q x) := by
  apply Finset.disjoint_left.mpr
  intro a hA hB
  have h := (Finset.mem_filter.mp hA).2
  have H := (Finset.mem_filter.mp hB).2
  omega
theorem before_succ (p : Finset ℕ) (x : ℕ) (hx : x ∈ p) :
    before p (x+1) = insert x (before p x) := by
  ext a
  simp only [before,Finset.mem_filter,Finset.mem_insert]
  constructor
  · intro ⟨ha,ht⟩
    by_cases h : a=x
    · exact Or.inl h
    · exact Or.inr ⟨ha,by omega⟩
  · rintro (rfl|⟨ha,ht⟩)
    · exact ⟨hx,by omega⟩
    · exact ⟨ha,by omega⟩
theorem before_no_self (p : Finset ℕ) (x : ℕ) : x ∉ before p x := by
  simp [before]
theorem srank_eq_iff {B : Finset ℕ} {k : ℕ} (p : Sel B k)
    (i : Fin k) (x : ℕ) :
    srank p i = x ↔ x ∈ p.val ∧ (before p.val x).card=i.val := by
  have h1 := indexedRank_before p.val (selCard p) i x
  have h2 := indexedRank_before p.val (selCard p) i (x+1)
  change srank p i < x ↔ i.val < (before p.val x).card at h1
  change srank p i < x+1 ↔ i.val < (before p.val (x+1)).card at h2
  constructor
  · intro h
    have hm : x∈p.val := h ▸ indexedRank_mem p.val (selCard p) i
    have H : (before p.val (x+1)).card = (before p.val x).card+1 := by
      rw [before_succ _ _ hm, Finset.card_insert_of_notMem (before_no_self _ _)]
    have U : ¬ i.val<(before p.val x).card := by rw [← h1,h]; omega
    have L := h2.mp (by omega)
    exact ⟨hm,by omega⟩
  · rintro ⟨hm,hc⟩
    have H : (before p.val (x+1)).card = (before p.val x).card+1 := by
      rw [before_succ _ _ hm, Finset.card_insert_of_notMem (before_no_self _ _)]
    have U : ¬ srank p i < x := by rw [h1,hc]; omega
    have L := h2.mpr (by omega)
    omega
theorem after_card_of_rank {B : Finset ℕ} {k : ℕ} (p : Sel B k) (i : Fin k)
    (x : ℕ) (h : srank p i=x) : (after p.val x).card=k-1-i.val := by
  have ⟨hm,hc⟩ := (srank_eq_iff p i x).1 h
  have H := congrArg Finset.card (before_after p.val x)
  rw [Finset.card_union_of_disjoint (before_after_disjoint _ _ _),
    hc,Finset.card_erase_of_mem hm,selCard p] at H
  omega
end AiresKahnSubset
#print axioms AiresKahnSubset.srank_eq_iff
namespace AiresKahnSubset
open scoped BigOperators
def rankSplit {B : Finset ℕ} {k : ℕ} (i : Fin k) (x : ℕ)
    (p : {p : Sel B k // srank p i = x}) :
    Sel (before B x) i.val × Sel (after B x) (k-1-i.val) := by
  have hcard := ((srank_eq_iff p.val i x).1 p.property).2
  have hs := (Finset.mem_powersetCard.mp p.val.property).1
  exact ⟨⟨before p.val.val x, Finset.mem_powersetCard.mpr
    ⟨Finset.filter_subset_filter _ hs,hcard⟩⟩,
    ⟨after p.val.val x,Finset.mem_powersetCard.mpr
    ⟨Finset.filter_subset_filter _ hs,after_card_of_rank _ _ _ p.property⟩⟩⟩
theorem rankSplit_bijective {B : Finset ℕ} {k : ℕ} (i : Fin k) {x : ℕ}
    (hx : x∈B) : Function.Bijective (rankSplit (B:=B) i x) := by
  constructor
  · intro p q hpq
    have hp := ((srank_eq_iff p.val i x).1 p.property).1
    have hq := ((srank_eq_iff q.val i x).1 q.property).1
    have he1 : before p.val.val x=before q.val.val x :=
      congrArg (fun a => a.1.val) hpq
    have he2 : after p.val.val x=after q.val.val x :=
      congrArg (fun a => a.2.val) hpq
    apply Subtype.ext
    apply Subtype.ext
    calc
      p.val.val = insert x (p.val.val.erase x) := (Finset.insert_erase hp).symm
      _ = insert x (q.val.val.erase x) := by rw [← before_after,he1,he2,before_after]
      _ = q.val.val := Finset.insert_erase hq
  · intro z
    have ha := Finset.mem_powersetCard.mp z.1.property
    have hb := Finset.mem_powersetCard.mp z.2.property
    have hd : Disjoint z.1.val z.2.val :=
      (before_after_disjoint B B x).mono ha.1 hb.1
    have hn : x ∉ z.1.val ∪ z.2.val := by
      intro H
      rcases Finset.mem_union.mp H with h|h
      · exact before_no_self _ _ (ha.1 h)
      · exact (Nat.lt_irrefl _ (Finset.mem_filter.mp (hb.1 h)).2)
    let s := insert x (z.1.val ∪ z.2.val)
    have hsubset : s⊆B := by
      intro a h
      rcases Finset.mem_insert.mp h with h|h
      · simpa [h] using hx
      · rcases Finset.mem_union.mp h with h|h
        · exact (Finset.mem_filter.mp (ha.1 h)).1
        · exact (Finset.mem_filter.mp (hb.1 h)).1
    have hc : s.card=k := by
      dsimp [s]
      rw [Finset.card_insert_of_notMem hn,Finset.card_union_of_disjoint hd,ha.2,hb.2]
      have hi := i.isLt
      omega
    have hbefore : before s x=z.1.val := by
      ext a
      simp only [before,s,Finset.mem_filter,Finset.mem_insert,Finset.mem_union]
      constructor
      · rintro ⟨h,ht⟩
        rcases h with h|h|h
        · omega
        · exact h
        · have H := (Finset.mem_filter.mp (hb.1 h)).2
          omega
      · intro h
        exact ⟨Or.inr (Or.inl h),(Finset.mem_filter.mp (ha.1 h)).2⟩
    have hafter : after s x=z.2.val := by
      ext a
      simp only [after,s,Finset.mem_filter,Finset.mem_insert,Finset.mem_union]
      constructor
      · rintro ⟨h,ht⟩
        rcases h with h|h|h
        · omega
        · have H := (Finset.mem_filter.mp (ha.1 h)).2
          omega
        · exact h
      · intro h
        exact ⟨Or.inr (Or.inr h),(Finset.mem_filter.mp (hb.1 h)).2⟩
    let p : Sel B k := ⟨s,Finset.mem_powersetCard.mpr ⟨hsubset,hc⟩⟩
    have hh : srank p i=x := (srank_eq_iff p i x).2
      ⟨Finset.mem_insert_self _ _,by change (before s x).card=i.val; rw [hbefore,ha.2]⟩
    refine ⟨⟨p,hh⟩,Prod.ext (Subtype.ext hbefore) (Subtype.ext hafter)⟩
noncomputable def rankSplitEquiv {B : Finset ℕ} {k : ℕ} (i : Fin k) {x : ℕ}
    (hx : x∈B) :
    {p : Sel B k // srank p i=x} ≃
      Sel (before B x) i.val × Sel (after B x) (k-1-i.val) :=
  Equiv.ofBijective _ (rankSplit_bijective i hx)
theorem rank_fiber_card {B : Finset ℕ} {k : ℕ} (i : Fin k) {x : ℕ} (hx : x∈B) :
    Fintype.card {p : Sel B k // srank p i=x} =
    (before B x).card.choose i.val * (after B x).card.choose (k-1-i.val) := by
  rw [Fintype.card_congr (rankSplitEquiv i hx),Fintype.card_prod]
  simp only [Sel,Fintype.card_coe,Finset.card_powersetCard]
end AiresKahnSubset
#print axioms AiresKahnSubset.rank_fiber_card
namespace AiresKahnSubset
open scoped BigOperators
abbrev interval (L : ℕ) := Finset.Icc 1 L
theorem srank_in {B : Finset ℕ} {k : ℕ} (p : Sel B k) (i : Fin k) :
    srank p i ∈ B :=
  (Finset.mem_powersetCard.mp p.property).1 (indexedRank_mem _ _ _)
def rankIndex {L k : ℕ} (i : Fin k) (p : Sel (interval L) k) : Fin L := by
  have h := Finset.mem_Icc.mp (srank_in p i)
  exact ⟨srank p i - 1, by omega⟩
theorem rankIndex_val {L k : ℕ} (i : Fin k) (p : Sel (interval L) k) :
    (rankIndex i p).val+1=srank p i := by
  have h := Finset.mem_Icc.mp (srank_in p i)
  change srank p i - 1 + 1 = srank p i
  omega
theorem rankIndex_eq {L k : ℕ} (i : Fin k) (p : Sel (interval L) k) (q : Fin L) :
    rankIndex i p = q ↔ srank p i=q.val+1 := by
  rw [← rankIndex_val i p]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Fin.ext (by omega)
def fiberEquiv {L k : ℕ} (i : Fin k) (q : Fin L) :
    {p : Sel (interval L) k // rankIndex i p=q} ≃
    {p : Sel (interval L) k // srank p i=q.val+1} where
  toFun p := ⟨p.val, (rankIndex_eq i p.val q).1 p.property⟩
  invFun p := ⟨p.val, (rankIndex_eq i p.val q).2 p.property⟩
  left_inv _p := Subtype.ext rfl
  right_inv _p := Subtype.ext rfl
theorem before_interval {L : ℕ} (q : Fin L) :
    before (interval L) (q.val+1) = Finset.Icc 1 q.val := by
  ext a
  simp only [before,interval,Finset.mem_filter,Finset.mem_Icc]
  have h := q.isLt
  omega
theorem after_interval {L : ℕ} (q : Fin L) :
    after (interval L) (q.val+1) = Finset.Icc (q.val+2) L := by
  ext a
  simp only [after,interval,Finset.mem_filter,Finset.mem_Icc]
  omega
theorem fiberIndex_count {L k : ℕ} (i : Fin k) (q : Fin L) :
    Fintype.card {p : Sel (interval L) k // rankIndex i p=q} =
      q.val.choose i.val * (L-1-q.val).choose (k-1-i.val) := by
  have hx : q.val+1 ∈ interval L := by
    apply Finset.mem_Icc.mpr
    have h := q.isLt
    omega
  rw [Fintype.card_congr (fiberEquiv i q),rank_fiber_card i hx,
      before_interval q,after_interval q,Nat.card_Icc,Nat.card_Icc]
  have h := q.isLt
  rw [show q.val+1-1=q.val by omega,show L+1-(q.val+2)=L-1-q.val by omega]
theorem rank_sum (n : ℕ) {k : ℕ} (i : Fin k) :
    (∑ p : Sel (interval (n+1)) k, srank p i) =
      (i.val+1)*(n+2).choose (k+1) := by
  let E := Equiv.sigmaFiberEquiv (rankIndex (L:=n+1) i)
  rw [← E.sum_comp (fun p => srank p i), Fintype.sum_sigma]
  have H : ∀ q : Fin (n+1), (∑ p : {p : Sel (interval (n+1)) k // rankIndex i p=q},
       srank (E ⟨q,p⟩) i) =
      (q.val+1)*q.val.choose i.val*(n-q.val).choose (k-1-i.val) := by
    intro q
    have he : ∀ p : {p : Sel (interval (n+1)) k // rankIndex i p=q},
        srank (E ⟨q,p⟩) i = q.val+1 := fun p => (rankIndex_eq i p.val q).1 p.property
    simp_rw [he]
    rw [Finset.sum_const,Finset.card_univ,fiberIndex_count]
    simp only [Nat.add_sub_cancel,nsmul_eq_mul,Nat.cast_id]
    ring
  simp_rw [H]
  rw [Fin.sum_univ_eq_sum_range (fun q => (q+1)*q.choose i.val*(n-q).choose (k-1-i.val)),
    AiresKahnLocal.rankWeight_total]
  have hh := i.isLt
  rw [show i.val+(k-1-i.val)+2=k+1 by omega]
theorem rank_mean (n : ℕ) {k : ℕ} (i : Fin k) (hk : k≤n+1) :
    ((∑ p : Sel (interval (n+1)) k, (srank p i:ℚ)) /
      (Fintype.card (Sel (interval (n+1)) k):ℚ)) =
        ((i.val:ℚ)+1)*((n:ℚ)+2)/((k:ℚ)+1) := by
  rw [← Nat.cast_sum,rank_sum]
  simp only [interval,Sel,Fintype.card_coe,Finset.card_powersetCard,Nat.card_Icc,
    Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have A : ((n+1).choose k:ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have B : (0:ℚ) < (k:ℚ)+1 := by positivity
  have H := congrArg (fun x : ℕ => (x:ℚ)) (AiresKahnLocal.rankWeight_mul (n+1) k)
  push_cast at H
  change ((n:ℚ)+1+1)*((n+1).choose k:ℚ) =
    ((k:ℚ)+1)*((n+2).choose (k+1):ℚ) at H
  field_simp [A,B.ne']
  linear_combination -H
end AiresKahnSubset
#print axioms AiresKahnSubset.rank_sum
#print axioms AiresKahnSubset.rank_mean
namespace AiresKahnFamily
open AiresKahnSubset
open scoped BigOperators
abbrev m (n : ℕ) := 2*n+1
abbrev slot (n : ℕ) := interval (2*m n)
abbrev Full (n : ℕ) := Sel (slot n) (m n)
def mid (n : ℕ) : Fin (m n) := ⟨n,by dsimp [m]; omega⟩
theorem base_card (n : ℕ) : (slot n).card = 2*m n := by
  simp [slot,interval,Nat.card_Icc]
theorem before_mid (n : ℕ) : before (slot n) (m n+1) = interval (m n) := by
  ext x
  simp only [before,slot,interval,Finset.mem_filter,Finset.mem_Icc]
  omega
def comp {n : ℕ} (p : Full n) : Full n := by
  have hp := (Finset.mem_powersetCard.mp p.property).1
  refine ⟨slot n \ p.val,Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset,?_⟩⟩
  rw [Finset.card_sdiff_of_subset hp,base_card,selCard p]
  omega
theorem comp_involution {n : ℕ} (p : Full n) : comp (comp p)=p := by
  apply Subtype.ext
  exact Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp p.property).1
def prefixes {n : ℕ} (p : Full n) := (before p.val (m n+1)).card
theorem prefix_partition {n : ℕ} (p : Full n) :
    prefixes p+prefixes (comp p)=m n := by
  have H : before (comp p).val (m n+1)
      = before (slot n) (m n+1) \ before p.val (m n+1) := by
    ext x
    simp only [before,comp,Finset.mem_filter,Finset.mem_sdiff]
    tauto
  have hp := (Finset.mem_powersetCard.mp p.property).1
  have H' := Finset.card_sdiff_of_subset (Finset.filter_subset_filter (· < m n+1) hp)
  change (before (slot n) (m n+1) \ before p.val (m n+1)).card =
    (before (slot n) (m n+1)).card - (before p.val (m n+1)).card at H'
  have hb : (before (slot n) (m n+1)).card=m n := by
    rw [before_mid]; simp [interval,Nat.card_Icc]
  have hc := Finset.card_le_card (Finset.filter_subset_filter (· < m n+1) hp)
  change (before p.val (m n+1)).card≤(before (slot n) (m n+1)).card at hc
  unfold prefixes
  rw [H,H',hb]
  omega
def aMid {n : ℕ} (p : Full n) : ℕ := srank p (mid n)
def bMid {n : ℕ} (p : Full n) : ℕ := srank (comp p) (mid n)
theorem mid_before {n : ℕ} (p : Full n) :
    aMid p≤ m n ↔ n+1≤prefixes p := by
  have H := indexedRank_before p.val (selCard p) (mid n) (m n+1)
  change aMid p< m n+1 ↔ n<prefixes p at H
  omega
theorem aMid_lt_bMid {n : ℕ} (p : Full n) :
    aMid p<bMid p ↔ n+1≤prefixes p := by
  have H := prefix_partition p
  have A := mid_before p
  have B := mid_before (comp p)
  change bMid p≤ m n ↔ n+1≤prefixes (comp p) at B
  dsimp [m] at *
  omega
abbrev Deleted (n : ℕ) := {p : Full n // aMid p < bMid p}
theorem deleted_positions {n : ℕ} (p : Deleted n) :
    aMid p.val ≤ m n ∧ m n < bMid p.val := by
  have h := (aMid_lt_bMid p.val).1 p.property
  have H := prefix_partition p.val
  have A := mid_before p.val
  have B := mid_before (comp p.val)
  change bMid p.val≤ m n ↔ n+1≤prefixes (comp p.val) at B
  dsimp [m] at *
  omega
end AiresKahnFamily
#print axioms AiresKahnFamily.aMid_lt_bMid
namespace AiresKahnSubset
theorem selSub {B : Finset ℕ} {k : ℕ} (p : Sel B k) : p.val ⊆ B :=
  (Finset.mem_powersetCard.mp p.property).1
def relabel {B C : Finset ℕ} {k : ℕ} (f : ℕ → ℕ)
    (hf : ∀ x∈B, f x∈C) (hi : Set.InjOn f ↑B) (p : Sel B k) : Sel C k :=
  ⟨p.val.image f,Finset.mem_powersetCard.mpr
    ⟨Finset.image_subset_iff.mpr (fun x hx => hf x (selSub p hx)),
      (Finset.card_image_of_injOn (hi.mono (fun _ h => selSub p h))).trans (selCard p)⟩⟩
def relabelEquiv {B C : Finset ℕ} {k : ℕ} (f g : ℕ → ℕ)
    (hf : ∀ x∈B, f x∈C) (hg : ∀ x∈C, g x∈B)
    (hgf : ∀ x∈B, g (f x)=x) (hfg : ∀ x∈C, f (g x)=x) :
      Sel B k ≃ Sel C k := by
  have hi : Set.InjOn f ↑B := by
    intro a ha b hb h
    exact (hgf a ha).symm.trans ((congrArg g h).trans (hgf b hb))
  have hj : Set.InjOn g ↑C := by
    intro a ha b hb h
    exact (hfg a ha).symm.trans ((congrArg f h).trans (hfg b hb))
  refine ⟨relabel f hf hi, relabel g hg hj, ?_,?_⟩
  · intro p
    apply Subtype.ext
    change (p.val.image f).image g=p.val
    rw [Finset.image_image]
    trans p.val.image id
    · exact Finset.image_congr (fun x hx => hgf x (selSub p hx))
    · exact Finset.image_id
  · intro p
    apply Subtype.ext
    change (p.val.image g).image f=p.val
    rw [Finset.image_image]
    trans p.val.image id
    · exact Finset.image_congr (fun x hx => hfg x (selSub p hx))
    · exact Finset.image_id
theorem before_image {p : Finset ℕ} (f : ℕ → ℕ) (x : ℕ)
    (h : ∀ a∈p, f a < f x ↔ a<x) :
    before (p.image f) (f x) = (before p x).image f := by
  ext z
  simp only [before,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨a,ha,rfl⟩,hz⟩
    exact ⟨a,⟨ha,(h a ha).1 hz⟩,rfl⟩
  · rintro ⟨a,⟨ha,ht⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,(h a ha).2 ht⟩
theorem before_image_rev {p : Finset ℕ} (f : ℕ → ℕ) (x : ℕ)
    (h : ∀ a∈p, f a < f x ↔ x<a) :
    before (p.image f) (f x) = (after p x).image f := by
  ext z
  simp only [before,after,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨a,ha,rfl⟩,hz⟩
    exact ⟨a,⟨ha,(h a ha).1 hz⟩,rfl⟩
  · rintro ⟨a,⟨ha,ht⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,(h a ha).2 ht⟩
theorem rank_relabel {B C : Finset ℕ} {k : ℕ} (f : ℕ → ℕ)
    (hf : ∀ x∈B, f x∈C) (hi : Set.InjOn f ↑B)
    (H : ∀ a∈B, ∀ b∈B, f a<f b ↔ a<b) (p : Sel B k) (i : Fin k) :
    srank (relabel f hf hi p) i = f (srank p i) := by
  let x := srank p i
  have hx := (srank_eq_iff p i x).1 rfl
  refine (srank_eq_iff _ _ _).2 ⟨Finset.mem_image.mpr ⟨x,hx.1,rfl⟩,?_⟩
  change (before (p.val.image f) (f x)).card=i.val
  rw [before_image f x (fun a ha => H a (selSub p ha) x (selSub p hx.1))]
  rw [Finset.card_image_of_injOn]
  · exact hx.2
  · intro a ha b hb h
    exact hi (selSub p (Finset.mem_filter.mp ha).1) (selSub p (Finset.mem_filter.mp hb).1) h
def revIndex {k : ℕ} (i : Fin k) : Fin k := ⟨k-1-i.val,by have H := i.isLt; omega⟩
theorem rank_relabel_rev {B C : Finset ℕ} {k : ℕ} (f : ℕ → ℕ)
    (hf : ∀ x∈B, f x∈C) (hi : Set.InjOn f ↑B)
    (H : ∀ a∈B, ∀ b∈B, f a<f b ↔ b<a) (p : Sel B k) (i : Fin k) :
    srank (relabel f hf hi p) i = f (srank p (revIndex i)) := by
  let j := revIndex i
  let x := srank p j
  have hx := (srank_eq_iff p j x).1 rfl
  refine (srank_eq_iff _ _ _).2 ⟨Finset.mem_image.mpr ⟨x,hx.1,rfl⟩,?_⟩
  change (before (p.val.image f) (f x)).card=i.val
  rw [before_image_rev f x (fun a ha => H a (selSub p ha) x (selSub p hx.1))]
  rw [Finset.card_image_of_injOn]
  · rw [after_card_of_rank p j x rfl]
    have hi' := i.isLt
    change k-1-(k-1-i.val)=i.val
    omega
  · intro a ha b hb h
    exact hi (selSub p (Finset.mem_filter.mp ha).1) (selSub p (Finset.mem_filter.mp hb).1) h
end AiresKahnSubset
#print axioms AiresKahnSubset.rank_relabel
#print axioms AiresKahnSubset.rank_relabel_rev
namespace AiresKahnFamily
open AiresKahnSubset
def reflectPos (n : ℕ) (x : ℕ) := 2*m n+1-x
theorem reflectPos_mem (n : ℕ) (x : ℕ) (hx : x∈slot n) : reflectPos n x∈slot n := by
  have h := Finset.mem_Icc.mp hx
  apply Finset.mem_Icc.mpr
  dsimp [reflectPos,slot] at *
  omega
theorem reflectPos_twice (n : ℕ) (x : ℕ) (hx : x∈slot n) :
    reflectPos n (reflectPos n x)=x := by
  have h := Finset.mem_Icc.mp hx
  dsimp [reflectPos,slot] at *
  omega
def reflectFull (n : ℕ) : Full n ≃ Full n :=
  relabelEquiv (reflectPos n) (reflectPos n) (reflectPos_mem n)
    (reflectPos_mem n) (reflectPos_twice n) (reflectPos_twice n)
theorem reflectFull_mid {n : ℕ} (p : Full n) :
    aMid (reflectFull n p)=reflectPos n (aMid p) := by
  have hi : Set.InjOn (reflectPos n) ↑(slot n) := by
    intro a ha b hb h
    exact (reflectPos_twice n a ha).symm.trans ((congrArg (reflectPos n) h).trans
      (reflectPos_twice n b hb))
  have hanti : ∀ (a : ℕ), a∈slot n → ∀ b∈slot n,
      reflectPos n a<reflectPos n b ↔ b<a := by
    intro a ha b hb
    have h1 := Finset.mem_Icc.mp ha
    have h2 := Finset.mem_Icc.mp hb
    dsimp [slot,reflectPos] at *
    omega
  have H := rank_relabel_rev _ (reflectPos_mem n) hi hanti p (mid n)
  have h : revIndex (mid n)=mid n := by
    apply Fin.ext
    change m n-1-n=n
    dsimp [m]
    omega
  rw [h] at H
  exact H
theorem reflectFull_comp {n : ℕ} (p : Full n) :
    reflectFull n (comp p)=comp (reflectFull n p) := by
  apply Subtype.ext
  change Finset.image (reflectPos n) (slot n \ p.val) =
    slot n \ Finset.image (reflectPos n) p.val
  ext x
  simp only [Finset.mem_image,Finset.mem_sdiff]
  constructor
  · rintro ⟨y,⟨hy,hp⟩,rfl⟩
    refine ⟨reflectPos_mem n y hy,?_⟩
    rintro ⟨z,hz,heq⟩
    have H := congrArg (reflectPos n) heq
    rw [reflectPos_twice n z (selSub p hz),reflectPos_twice n y hy] at H
    exact hp (H ▸ hz)
  · rintro ⟨hx,hn⟩
    refine ⟨reflectPos n x,⟨reflectPos_mem n x hx,?_⟩,reflectPos_twice n x hx⟩
    intro hm
    exact hn ⟨_,hm,reflectPos_twice n x hx⟩
def swapReverse {n : ℕ} (p : Deleted n) : Deleted n := by
  refine ⟨reflectFull n (comp p.val),?_⟩
  have h := p.property
  have h1 := reflectFull_mid (comp p.val)
  have h2 := reflectFull_mid p.val
  have ha := Finset.mem_Icc.mp (srank_in p.val (mid n))
  have hb := Finset.mem_Icc.mp (srank_in (comp p.val) (mid n))
  change 1≤aMid p.val ∧ aMid p.val≤2*m n at ha
  change 1≤bMid p.val ∧ bMid p.val≤2*m n at hb
  change aMid (reflectFull n (comp p.val)) <
    aMid (comp (reflectFull n (comp p.val))) 
  rw [h1,←reflectFull_comp,comp_involution,h2]
  change aMid p.val<bMid p.val at h
  have h1' := ha.2
  have h2' := hb.2
  change reflectPos n (bMid p.val)<reflectPos n (aMid p.val)
  unfold reflectPos
  omega
theorem reflectFull_twice {n : ℕ} (p : Full n) :
    reflectFull n (reflectFull n p)=p := by
  apply Subtype.ext
  change (p.val.image (reflectPos n)).image (reflectPos n)=p.val
  rw [Finset.image_image]
  trans p.val.image id
  · exact Finset.image_congr (fun x hx => reflectPos_twice n x (selSub p hx))
  · exact Finset.image_id
theorem swapReverse_involutive {n : ℕ} : Function.Involutive (@swapReverse n) := by
  intro p
  apply Subtype.ext
  change reflectFull n (comp (reflectFull n (comp p.val)))=p.val
  rw [←reflectFull_comp,comp_involution,reflectFull_twice]
def swapReverseEquiv (n : ℕ) : Deleted n ≃ Deleted n :=
  ⟨swapReverse,swapReverse,swapReverse_involutive,swapReverse_involutive⟩
theorem swapReverse_a {n : ℕ} (p : Deleted n) :
    aMid (swapReverse p).val=reflectPos n (bMid p.val) :=
  reflectFull_mid (comp p.val)
theorem swapReverse_b {n : ℕ} (p : Deleted n) :
    bMid (swapReverse p).val=reflectPos n (aMid p.val) := by
  change aMid (comp (reflectFull n (comp p.val)))=_
  rw [←reflectFull_comp,comp_involution,reflectFull_mid]
end AiresKahnFamily
#print axioms AiresKahnFamily.swapReverse_a
#print axioms AiresKahnFamily.swapReverse_b
namespace AiresKahnFamily
open AiresKahnSubset
open scoped BigOperators
abbrev tail (n : ℕ) := Finset.Icc (m n+1) (2*m n)
def tIndex {n : ℕ} (p : Deleted n) : Fin (n+1) := by
  have h := (aMid_lt_bMid p.val).1 p.property
  have H := prefix_partition p.val
  exact ⟨prefixes p.val-(n+1),by dsimp [m] at H; omega⟩
def tSize {n : ℕ} (i : Fin (n+1)) := n+1+i.val
theorem tSize_eq {n : ℕ} (p : Deleted n) : tSize (tIndex p)=prefixes p.val := by
  have h := (aMid_lt_bMid p.val).1 p.property
  change n+1+(prefixes p.val-(n+1))=prefixes p.val
  omega
theorem tail_card (n : ℕ) : (tail n).card=m n := by
  simp only [tail,Nat.card_Icc]
  omega
theorem tail_of_full (n : ℕ) : after (slot n) (m n)=tail n := by
  ext x
  simp only [after,slot,interval,tail,Finset.mem_filter,Finset.mem_Icc]
  omega
theorem full_partition (n : ℕ) : interval (m n) ∪ tail n=slot n := by
  ext x
  simp only [interval,tail,slot,Finset.mem_union,Finset.mem_Icc]
  omega
theorem parts_disjoint (n : ℕ) : Disjoint (interval (m n)) (tail n) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have h := Finset.mem_Icc.mp ha
  have H := Finset.mem_Icc.mp hb
  omega
theorem before_after_partition (p : Finset ℕ) (x : ℕ) :
    before p (x+1) ∪ after p x = p := by
  ext a
  simp only [before,after,Finset.mem_union,Finset.mem_filter]
  constructor
  · rintro (⟨h,_⟩|⟨h,_⟩) <;> exact h
  · intro h
    by_cases H : a≤x
    · exact Or.inl ⟨h,by omega⟩
    · exact Or.inr ⟨h,by omega⟩
theorem after_full_partition {n : ℕ} (p : Full n) :
    (after p.val (m n)).card = m n-prefixes p := by
  have h := congrArg Finset.card (before_after_partition p.val (m n))
  have hd : Disjoint (before p.val (m n+1)) (after p.val (m n)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have H := (Finset.mem_filter.mp ha).2
    have J := (Finset.mem_filter.mp hb).2
    omega
  rw [Finset.card_union_of_disjoint hd,selCard p] at h
  change prefixes p+(after p.val (m n)).card=m n at h
  omega
abbrev HalfPair (n : ℕ) :=
  Σ i : Fin (n+1), Sel (interval (m n)) (tSize i) × Sel (tail n) (tSize i)
def halfSplit {n : ℕ} (p : Deleted n) : HalfPair n := by
  refine ⟨tIndex p,⟨⟨before p.val.val (m n+1), Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩,
    ⟨after (comp p.val).val (m n), Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩⟩⟩
  · rw [← before_mid]
    exact Finset.filter_subset_filter _ (selSub p.val)
  · exact (tSize_eq p).symm
  · rw [← tail_of_full]
    exact Finset.filter_subset_filter _ (selSub (comp p.val))
  · rw [after_full_partition,tSize_eq]
    have H := prefix_partition p.val
    omega
theorem tail_comp {n : ℕ} (p : Full n) :
    after (comp p).val (m n)=tail n \ after p.val (m n) := by
  ext a
  rw [← tail_of_full]
  simp only [after,comp,Finset.mem_filter,Finset.mem_sdiff]
  tauto
theorem halfSplit_injective {n : ℕ} : Function.Injective (@halfSplit n) := by
  intro p q h
  have F : before p.val.val (m n+1)=before q.val.val (m n+1) :=
    congrArg (fun z : HalfPair n => z.2.1.val) h
  have G : after (comp p.val).val (m n)=after (comp q.val).val (m n) :=
    congrArg (fun z : HalfPair n => z.2.2.val) h
  have Jp := tail_comp (comp p.val)
  have Jq := tail_comp (comp q.val)
  rw [comp_involution] at Jp Jq
  have H : after p.val.val (m n)=after q.val.val (m n) := by rw [Jp,Jq,G]
  apply Subtype.ext
  apply Subtype.ext
  rw [← before_after_partition p.val.val (m n),← before_after_partition q.val.val (m n),F,H]
end AiresKahnFamily
#print axioms AiresKahnFamily.halfSplit_injective
namespace AiresKahnFamily
open AiresKahnSubset
open scoped BigOperators
theorem halfPair_heq {n : ℕ} {i j : Fin (n+1)}
    (h : i=j)
    (p : Sel (interval (m n)) (tSize i) × Sel (tail n) (tSize i))
    (q : Sel (interval (m n)) (tSize j) × Sel (tail n) (tSize j))
    (h1 : p.1.val=q.1.val) (h2 : p.2.val=q.2.val) : HEq p q := by
  subst j
  exact heq_of_eq (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
theorem halfSplit_surjective {n : ℕ} : Function.Surjective (@halfSplit n) := by
  intro z
  rcases z with ⟨i,pre,bs⟩
  let A := pre.val ∪ (tail n \ bs.val)
  have hdis : Disjoint pre.val (tail n \ bs.val) :=
    (parts_disjoint n).mono (selSub pre) Finset.sdiff_subset
  have hc : A.card=m n := by
    dsimp [A]
    rw [Finset.card_union_of_disjoint hdis,selCard pre,
      Finset.card_sdiff_of_subset (selSub bs),tail_card,selCard bs]
    have hi:=i.isLt
    dsimp [tSize,m]
    omega
  have hsub : A⊆slot n := by
    rw [← full_partition]
    exact Finset.union_subset
       ((selSub pre).trans Finset.subset_union_left)
       (Finset.sdiff_subset.trans Finset.subset_union_right)
  let p : Full n := ⟨A,Finset.mem_powersetCard.mpr ⟨hsub,hc⟩⟩
  have hpre : before p.val (m n+1)=pre.val := by
    ext u
    simp only [p,A,before,Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro ⟨h,ht⟩
      rcases h with h|⟨h,_⟩
      · exact h
      · have H := (Finset.mem_Icc.mp h).1
        omega
    · intro h
      have H := (Finset.mem_Icc.mp (selSub pre h)).2
      exact ⟨Or.inl h,by omega⟩
  have htail : after p.val (m n)=tail n \ bs.val := by
    ext u
    simp only [p,A,after,Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro ⟨h,ht⟩
      rcases h with h|h
      · have H := (Finset.mem_Icc.mp (selSub pre h)).2
        omega
      · exact h
    · intro h
      have H := (Finset.mem_Icc.mp h.1).1
      exact ⟨Or.inr h,by omega⟩
  have H : prefixes p=tSize i := by unfold prefixes; rw [hpre,selCard pre]
  have H' : aMid p<bMid p := (aMid_lt_bMid p).2 (by rw [H]; unfold tSize; omega)
  let d : Deleted n := ⟨p,H'⟩
  have J : tIndex d=i := by
    apply Fin.ext
    change prefixes p-(n+1)=i.val
    rw [H]
    unfold tSize
    omega
  have hB : after (comp p).val (m n)=bs.val := by
    rw [tail_comp,htail,Finset.sdiff_sdiff_eq_self (selSub bs)]
  refine ⟨d,?_⟩
  apply Sigma.ext_iff.2
  refine ⟨J,?_⟩
  exact halfPair_heq J (halfSplit d).2 (pre,bs) hpre hB
end AiresKahnFamily
#print axioms AiresKahnFamily.halfSplit_surjective
namespace AiresKahnFamily
open AiresKahnSubset
open scoped BigOperators
noncomputable def halfEquiv (n : ℕ) : Deleted n ≃ HalfPair n :=
  Equiv.ofBijective halfSplit ⟨halfSplit_injective,halfSplit_surjective⟩
def iFin {n : ℕ} (i : Fin (n+1)) : Fin (tSize i) := ⟨i.val,by unfold tSize; omega⟩
def nFin {n : ℕ} (i : Fin (n+1)) : Fin (tSize i) := ⟨n,by unfold tSize; omega⟩
theorem splitAMid {n : ℕ} (p : Deleted n) :
    srank (halfSplit p).2.1 (nFin (tIndex p)) = aMid p.val := by
  have hm := (deleted_positions p).1
  have H := (srank_eq_iff p.val (mid n) (aMid p.val)).1 rfl
  refine (srank_eq_iff _ _ _).2 ⟨?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨H.1,by omega⟩
  · have K : before (before p.val.val (m n+1)) (aMid p.val) =
        before p.val.val (aMid p.val) := by
      ext x
      simp only [before,Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,by omega⟩,h.2⟩
    change (before (before p.val.val (m n+1)) (aMid p.val)).card=n
    rw [K]
    exact H.2
theorem splitBMid {n : ℕ} (p : Deleted n) :
    srank (halfSplit p).2.2 (iFin (tIndex p)) = bMid p.val := by
  let b := comp p.val
  let q := bMid p.val
  have hq : m n < q := (deleted_positions p).2
  have H := (srank_eq_iff b (mid n) q).1 rfl
  refine (srank_eq_iff _ _ _).2 ⟨Finset.mem_filter.mpr ⟨H.1,hq⟩,?_⟩
  have U : before b.val q =
      before b.val (m n+1) ∪ before (after b.val (m n)) q := by
    ext x
    simp only [before,after,Finset.mem_union,Finset.mem_filter]
    constructor
    · intro h
      by_cases t : x≤ m n
      · exact Or.inl ⟨h.1,by omega⟩
      · exact Or.inr ⟨⟨h.1,by omega⟩,h.2⟩
    · rintro (⟨h,t⟩|⟨⟨h,t⟩,u⟩)
      · exact ⟨h,by omega⟩
      · exact ⟨h,u⟩
  have D : Disjoint (before b.val (m n+1)) (before (after b.val (m n)) q) := by
    apply Finset.disjoint_left.mpr
    intro u ha hb
    have j := (Finset.mem_filter.mp ha).2
    have k := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    omega
  have L := H.2
  rw [U,Finset.card_union_of_disjoint D] at L
  change prefixes (comp p.val)+(before (after b.val (m n)) q).card=n at L
  have J := prefix_partition p.val
  have K := tSize_eq p
  change (before (after b.val (m n)) q).card=(tIndex p).val
  dsimp [m,tSize] at J K
  omega
end AiresKahnFamily
#print axioms AiresKahnFamily.splitAMid
#print axioms AiresKahnFamily.splitBMid
namespace AiresKahnLocal
open scoped BigOperators
section Uniform
variable (ι : Type) [Fintype ι]
def uniform (_i : ι) : ℚ := 1/(Fintype.card ι:ℚ)
theorem uniform_nonneg (i : ι) : 0≤uniform ι i := by unfold uniform; positivity
theorem uniform_sum [Nonempty ι] : ∑ i, uniform ι i=1 := by
  have h : (Fintype.card ι:ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniform,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [h]
theorem uniform_mean (f : ι → ℚ) :
    wmean (uniform ι) f = (∑ i, f i)/(Fintype.card ι:ℚ) := by
  unfold wmean uniform
  rw [← Finset.mul_sum]
  ring
theorem uniform_transport {κ : Type} [Fintype κ] (e : ι ≃ κ) (f : κ → ℚ) :
    wmean (uniform ι) (fun i => f (e i)) = wmean (uniform κ) f := by
  rw [uniform_mean,uniform_mean,e.sum_comp, Fintype.card_congr e]
end Uniform
section Prod
variable {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
theorem uniform_prod_left (f : ι → ℚ) :
    wmean (uniform (ι×κ)) (fun z => f z.1) = wmean (uniform ι) f := by
  rw [uniform_mean,uniform_mean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have h : (Fintype.card κ:ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [h]
theorem uniform_prod_right (f : κ → ℚ) :
    wmean (uniform (ι×κ)) (fun z => f z.2) = wmean (uniform κ) f := by
  have h := uniform_transport (ι×κ) (Equiv.prodComm ι κ) (fun z => f z.1)
  exact h.trans (uniform_prod_left (κ:=ι) f)
end Prod
section Sigma
variable {ι : Type} [Fintype ι] {β : ι → Type} [∀ i, Fintype (β i)]
def groupWeight (i : ι) : ℚ := (Fintype.card (β i):ℚ)/(Fintype.card (Sigma β):ℚ)
theorem groupWeight_nonneg (i : ι) : 0≤groupWeight (β:=β) i := by unfold groupWeight; positivity
theorem uniform_joint (hβ : ∀ i, Nonempty (β i)) :
    uniform (Sigma β) = joint (groupWeight (β:=β)) (fun i => uniform (β i)) := by
  funext x
  have := hβ x.1
  have h : (Fintype.card (β x.1):ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniform joint groupWeight
  field_simp [h]
theorem groupWeight_sum [Nonempty ι] (hβ : ∀ i, Nonempty (β i)) :
    ∑ i, groupWeight (β:=β) i=1 := by
  have h : Nonempty (Sigma β) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    obtain ⟨j⟩ := hβ i
    exact ⟨⟨i,j⟩⟩
  have H := uniform_sum (Sigma β)
  rw [uniform_joint hβ, Fintype.sum_sigma] at H
  unfold joint at H
  have hme : ∀ i, (∑ j, groupWeight (β:=β) i*uniform (β i) j) =
      groupWeight (β:=β) i := by
    intro i
    have := hβ i
    rw [← Finset.mul_sum,uniform_sum,mul_one]
  simpa only [hme] using H
end Sigma
end AiresKahnLocal
#print axioms AiresKahnLocal.uniform_joint
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
open scoped BigOperators
abbrev PairAt (n : ℕ) (i : Fin (n+1)) :=
  Sel (interval (m n)) (tSize i) × Sel (tail n) (tSize i)
theorem t_bound {n : ℕ} (i : Fin (n+1)) : tSize i≤ m n := by
  unfold tSize m
  have h:=i.isLt
  omega
theorem sel_nonempty (B : Finset ℕ) {k : ℕ} (h : k≤B.card) : Nonempty (Sel B k) := by
  apply Fintype.card_pos_iff.mp
  rw [Fintype.card_coe,Finset.card_powersetCard]
  exact Nat.choose_pos h
theorem pair_nonempty {n : ℕ} (i : Fin (n+1)) : Nonempty (PairAt n i) := by
  have A := sel_nonempty (interval (m n)) (k:=tSize i) (by
    simpa [interval,Nat.card_Icc] using t_bound i)
  have B := sel_nonempty (tail n) (k:=tSize i) (by rw [tail_card]; exact t_bound i)
  exact ⟨(A.some,B.some)⟩
def tailShift (n k : ℕ) : Sel (interval (m n)) k ≃ Sel (tail n) k :=
  relabelEquiv (fun x=>m n+x) (fun x=>x-m n)
    (fun x hx => by have H:=Finset.mem_Icc.mp hx; apply Finset.mem_Icc.mpr; omega)
    (fun x hx => by have H:=Finset.mem_Icc.mp hx; apply Finset.mem_Icc.mpr; omega)
    (fun x _ => by omega)
    (fun x hx => by have H:=Finset.mem_Icc.mp hx; omega)
theorem tailShift_rank {n k : ℕ} (p : Sel (interval (m n)) k) (i : Fin k) :
    srank (tailShift n k p) i=m n+srank p i := by
  have H := rank_relabel (fun x=>m n+x)
    (C:=tail n)
    (fun x hx => by have h:=Finset.mem_Icc.mp hx; apply Finset.mem_Icc.mpr; omega)
    (fun x _ y _ h => by dsimp at h; omega)
    (fun x _ y _ => by omega) p i
  exact H
theorem interval_mean {n : ℕ} (i : Fin (n+1)) (j : Fin (tSize i)) :
    wmean (uniform (Sel (interval (m n)) (tSize i))) (fun p => (srank p j:ℚ)) =
    ((j.val:ℚ)+1)*(2*(n:ℚ)+2)/((tSize i:ℚ)+1) := by
  rw [uniform_mean]
  have Q := rank_mean (2*n) j (t_bound i)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using Q
theorem tail_mean {n : ℕ} (i : Fin (n+1)) (j : Fin (tSize i)) :
    wmean (uniform (Sel (tail n) (tSize i))) (fun p => (srank p j:ℚ)) =
    (m n:ℚ)+((j.val:ℚ)+1)*(2*(n:ℚ)+2)/((tSize i:ℚ)+1) := by
  rw [← uniform_transport _ (tailShift n (tSize i))]
  simp_rw [tailShift_rank,Nat.cast_add]
  rw [wmean_add,wmean_const]
  · rw [interval_mean]
  · have := sel_nonempty (interval (m n)) (k:=tSize i) (by
      simpa [interval,Nat.card_Icc] using t_bound i)
    exact uniform_sum _
def halfGap {n : ℕ} (z : HalfPair n) : ℚ :=
  (srank z.2.2 (iFin z.1):ℚ) - (srank z.2.1 (nFin z.1):ℚ)
def gap {n : ℕ} (p : Deleted n) : ℚ := (bMid p.val:ℚ)-(aMid p.val:ℚ)
theorem halfGap_eq {n : ℕ} (p : Deleted n) : halfGap (halfEquiv n p)=gap p := by
  change (srank (halfSplit p).2.2 (iFin (tIndex p)):ℚ) -
    (srank (halfSplit p).2.1 (nFin (tIndex p)):ℚ) = _
  rw [splitAMid,splitBMid]
  rfl
def dval {n : ℕ} (i : Fin (n+1)) : ℚ := (i.val:ℚ)+1
theorem fiber_gap_mean {n : ℕ} (i : Fin (n+1)) :
    wmean (uniform (PairAt n i)) (fun z => halfGap ⟨i,z⟩) =
    4*((n:ℚ)+1)*dval i / (((n:ℚ)+1)+dval i)-1 := by
  have H := pair_nonempty i
  have A : Nonempty (Sel (interval (m n)) (tSize i)) := ⟨H.some.1⟩
  have B : Nonempty (Sel (tail n) (tSize i)) := ⟨H.some.2⟩
  change wmean (uniform (PairAt n i))
    (fun z => (srank z.2 (iFin i):ℚ)-(srank z.1 (nFin i):ℚ)) = _
  rw [wmean_sub,
    uniform_prod_right (ι:=Sel (interval (m n)) (tSize i))
      (fun p : Sel (tail n) (tSize i) => (srank p (iFin i):ℚ)),
    uniform_prod_left (κ:=Sel (tail n) (tSize i))
      (fun p : Sel (interval (m n)) (tSize i) => (srank p (nFin i):ℚ)),
    tail_mean,interval_mean]
  dsimp [dval,iFin,nFin,tSize,m]
  push_cast
  have h : (0:ℚ)<(n:ℚ)+1+(i.val:ℚ)+1 := by positivity
  have h' : (0:ℚ)<(n:ℚ)+1+((i.val:ℚ)+1) := by positivity
  field_simp [h.ne',h'.ne']
  ring
end AiresKahnFamily
#print axioms AiresKahnFamily.fiber_gap_mean
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
open scoped BigOperators
abbrev w (n : ℕ) := groupWeight (β:=PairAt n)
theorem pair_card {n : ℕ} (i : Fin (n+1)) :
    (Fintype.card (PairAt n i):ℚ)=chooseWeight (m n) (tSize i) := by
  rw [Fintype.card_prod,Nat.cast_mul]
  rw [Fintype.card_coe, Fintype.card_coe,Finset.card_powersetCard,Finset.card_powersetCard,tail_card]
  simp only [interval,Nat.card_Icc,Nat.add_sub_cancel,chooseWeight,pow_two]
theorem family_card (n : ℕ) :
    (Fintype.card (HalfPair n):ℚ) = central (m n)/2 := by
  rw [Fintype.card_sigma,Nat.cast_sum]
  simp_rw [pair_card,tSize]
  rw [Fin.sum_univ_eq_sum_range (fun t => chooseWeight (m n) (n+1+t))]
  exact mass_half n
theorem w_formula {n : ℕ} (i : Fin (n+1)) :
    w n i = chooseWeight (m n) (tSize i)/(central (m n)/2) := by
  unfold w groupWeight
  rw [pair_card,family_card]
def centerD {n : ℕ} (i : Fin (n+1)) : ℚ := dval i-1/2
theorem centered_first (n : ℕ) :
    wmean (w n) centerD=absMoment n := by
  unfold wmean
  simp_rw [w_formula,div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  dsimp [centerD,dval,tSize]
  rw [Fin.sum_univ_eq_sum_range
    (fun t => chooseWeight (m n) (n+1+t)*((t:ℚ)+1-1/2))]
  rw [← mass_half]
  convert half_centered_first n using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [m]
  push_cast
  ring
theorem centered_second (n : ℕ) (hn : 1≤n) :
    wmean (w n) (fun i => centerD i^2)=secondMoment n := by
  unfold wmean
  simp_rw [w_formula,div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  dsimp [centerD,dval,tSize]
  rw [Fin.sum_univ_eq_sum_range
    (fun t => chooseWeight (m n) (n+1+t)*((t:ℚ)+1-1/2)^2)]
  rw [← mass_half]
  convert half_centered_second n hn using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [m]
  push_cast
  ring
theorem w_sum (n : ℕ) : ∑ i,w n i=1 := groupWeight_sum pair_nonempty
theorem w_nonneg (n : ℕ) (i : Fin (n+1)) : 0≤w n i := groupWeight_nonneg i
theorem wmean_d (n : ℕ) : wmean (w n) dval=absMoment n+1/2 := by
  have H := centered_first n
  unfold centerD at H
  rw [wmean_sub,wmean_const _ (w_sum n)] at H
  linarith
theorem wvar_d (n : ℕ) (hn : 1≤n) :
    wvar (w n) dval=secondMoment n-(absMoment n)^2 := by
  have H : wvar (w n) dval=wvar (w n) centerD := by
    rw [← mul_right_inj' (show (2:ℚ)≠0 by norm_num),
      wvar_pairwise _ _ (w_sum n),wvar_pairwise _ _ (w_sum n)]
    congr 1
    funext i
    congr 1
    funext j
    unfold centerD
    ring
  rw [H,wvar,centered_first,centered_second n hn]
theorem dval_bounds {n : ℕ} (i : Fin (n+1)) :
    0≤dval i ∧ dval i≤(n:ℚ)+1 := by
  have h : (i.val:ℚ)≤(n:ℚ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  unfold dval
  constructor
  · positivity
  · linarith
theorem gap_variance (n : ℕ) (hn : 1≤n) :
    ((n:ℚ)+1)/40 ≤ wvar (uniform (Deleted n)) gap := by
  have h := foldedVar_lower n hn
  rw [← wvar_d n hn] at h
  apply h.trans
  have G : wvar (uniform (Deleted n)) gap = wvar (uniform (HalfPair n)) halfGap := by
    unfold wvar
    have a := uniform_transport (Deleted n) (halfEquiv n) halfGap
    have b := uniform_transport (Deleted n) (halfEquiv n) (fun z=>halfGap z^2)
    simp only [halfGap_eq] at a b
    rw [a,b]
  rw [G,uniform_joint (β:=PairAt n) pair_nonempty]
  apply le_trans _ (var_total_ge (w n) (fun i=>uniform (PairAt n i)) halfGap
    (w_nonneg n) (fun i=> by have := pair_nonempty i; exact uniform_sum _)
    (fun i j=>uniform_nonneg _ j))
  apply wvar_compare _ _ _ (w_sum n) (w_nonneg n)
  intro i j
  rw [fiber_gap_mean,fiber_gap_mean]
  exact conditional_mean_pairwise _ _ _ (by positivity)
    (dval_bounds j).1 (dval_bounds j).2 (dval_bounds i).1 (dval_bounds i).2
end AiresKahnFamily
#print axioms AiresKahnFamily.gap_variance
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
open scoped BigOperators
theorem deleted_nonempty (n : ℕ) : Nonempty (Deleted n) :=
  ⟨(halfEquiv n).symm ⟨0,(pair_nonempty 0).some⟩⟩
theorem gap_at_least_one {n : ℕ} (p : Deleted n) : 1≤gap p := by
  have h : aMid p.val+1≤bMid p.val := p.property
  unfold gap
  have H : (aMid p.val:ℚ)+1≤(bMid p.val:ℚ) := by exact_mod_cast h
  linarith
theorem gap_expectation_pos (n : ℕ) : 0 < wmean (uniform (Deleted n)) gap := by
  have := deleted_nonempty n
  have H := wmean_mono (uniform (Deleted n)) (fun _=>1) gap
    (uniform_nonneg _) gap_at_least_one
  rw [wmean_const _ (uniform_sum _)] at H
  linarith
theorem gap_expectation_le (n : ℕ) : wmean (uniform (Deleted n)) gap ≤ 4*wmean (w n) dval := by
  have H := uniform_transport (Deleted n) (halfEquiv n) halfGap
  simp only [halfGap_eq] at H
  rw [H,uniform_joint (β:=PairAt n) pair_nonempty,wmean_joint,←wmean_mul]
  apply wmean_mono _ _ _ (w_nonneg n)
  intro i
  rw [fiber_gap_mean]
  unfold dval
  have h : 0≤(i.val:ℚ)+1 := by positivity
  have h' : 0<((n:ℚ)+1)+((i.val:ℚ)+1) := by positivity
  have L : 4*((n:ℚ)+1)*((i.val:ℚ)+1) /
      (((n:ℚ)+1)+((i.val:ℚ)+1)) ≤ 4*((i.val:ℚ)+1) := by
    apply (div_le_iff₀ h').2
    nlinarith [sq_nonneg ((i.val:ℚ)+1)]
  linarith
theorem gap_expectation_scale (n h : ℕ) (hh : 1≤h) (hn : n+1=4*h^2) :
    wmean (uniform (Deleted n)) gap ≤ 8*(h:ℚ) := by
  have hq : (1:ℚ) ≤ (h:ℚ) := by exact_mod_cast hh
  have hn0 : 1≤n := by nlinarith
  have hn' := congrArg (fun x : ℕ => (x:ℚ)) hn
  push_cast at hn'
  have h2 := (hypergeom_variance_bounds ((n:ℚ)+1) (by exact_mod_cast (show 2≤n+1 by omega))).2
  have h2' : secondMoment n ≤ ((n:ℚ)+1)/4 := by
    convert h2 using 1
    unfold secondMoment
    ring_nf
  have hV := wvar_nonneg (w n) dval (w_sum n) (w_nonneg n)
  rw [wvar_d n hn0] at hV
  have hA := absMoment_pos n
  have ha : absMoment n≤(h:ℚ) := by
    by_contra! bad
    have diff : 0<(absMoment n-(h:ℚ))*(absMoment n+(h:ℚ)) :=
      mul_pos (sub_pos.mpr bad) (by linarith)
    nlinarith
  have H := gap_expectation_le n
  rw [wmean_d] at H
  linarith
theorem gap_bound_scale (n h : ℕ) (hh : 1≤h) (hn : n+1=4*h^2) :
    1+(h:ℚ)/320 ≤ 1+wvar (uniform (Deleted n)) gap /
      (4*wmean (uniform (Deleted n)) gap) := by
  have hn0 : 1≤n := by nlinarith
  have hn' := congrArg (fun x : ℕ => (x:ℚ)) hn
  push_cast at hn'
  apply shift_diverges_bound _ _ _ (by exact_mod_cast (show 0<h by omega))
    (gap_expectation_pos n)
  · rw [←hn']; exact gap_variance n hn0
  · exact gap_expectation_scale n h hh hn
end AiresKahnFamily
#print axioms AiresKahnFamily.gap_bound_scale
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
open scoped BigOperators
def gapNat {n : ℕ} (p : Deleted n) : ℕ := bMid p.val - aMid p.val
theorem gapNat_cast {n : ℕ} (p : Deleted n) : (gapNat p:ℚ)=gap p := by
  unfold gapNat gap
  exact Nat.cast_sub (show aMid p.val≤bMid p.val from p.property.le)
abbrev Marked (n : ℕ) := Σ p : Deleted n, Fin (gapNat p)
def marker {n : ℕ} (z : Marked n) : ℕ := aMid z.1.val + z.2.val + 1
def insertRank (x r : ℕ) : ℕ := if r<x then r else r+1
def bRank {n : ℕ} (j : Fin (m n)) (p : Deleted n) : ℕ := srank (comp p.val) j
def markedBRank {n : ℕ} (j : Fin (m n)) (z : Marked n) : ℕ :=
  insertRank (marker z) (bRank j z.1)
theorem marker_bounds {n : ℕ} (z : Marked n) :
    aMid z.1.val < marker z ∧ marker z ≤ bMid z.1.val := by
  have h := z.2.isLt
  have H : aMid z.1.val < bMid z.1.val := z.1.property
  dsimp [marker,gapNat] at *
  omega
theorem markedRank_incr {n : ℕ} (j : Fin (m n)) (hj : mid n≤j) (z : Marked n) :
    markedBRank j z=bRank j z.1+1 := by
  have H : bMid z.1.val ≤ bRank j z.1 :=
    (indexedRank_mono (comp z.1.val).val (selCard (comp z.1.val))).monotone hj
  unfold markedBRank insertRank
  rw [ite_eq_right (not_lt.mpr ((marker_bounds z).2.trans H))]
theorem marked_mean {n : ℕ} (j : Fin (m n)) (hj : mid n≤j) :
    wmean (uniform (Marked n)) (fun z => (markedBRank j z:ℚ)) =
      wmean (uniform (Deleted n)) (fun p => gap p*((bRank j p:ℚ)+1)) /
        wmean (uniform (Deleted n)) gap := by
  have H : (Fintype.card (Marked n):ℚ) = ∑ p : Deleted n, gap p := by
    rw [Fintype.card_sigma,Nat.cast_sum]
    simp only [Fintype.card_fin,gapNat_cast]
  rw [uniform_mean,Fintype.sum_sigma,H,uniform_mean,uniform_mean]
  simp_rw [markedRank_incr j hj,Nat.cast_add,Nat.cast_one,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,gapNat_cast]
  have ne : (Fintype.card (Deleted n):ℚ) ≠ 0 := by
     have := deleted_nonempty n
     exact_mod_cast Fintype.card_ne_zero
  rw [div_div_div_cancel_right₀ ne]
theorem weighting_shift {n : ℕ} (j : Fin (m n)) (hj : mid n≤j) :
    wmean (uniform (Marked n)) (fun z => (markedBRank j z:ℚ)) -
    wmean (uniform (Deleted n)) (fun p => (bRank j p:ℚ)) =
      1+covar (uniform (Deleted n)) (fun p => (bRank j p:ℚ)) gap /
         wmean (uniform (Deleted n)) gap := by
  rw [marked_mean j hj]
  have H : (fun p : Deleted n => gap p*((bRank j p:ℚ)+1)) =
      fun p => (bRank j p:ℚ)*gap p+gap p := by funext p; ring
  rw [H,wmean_add]
  unfold covar
  have ne := (gap_expectation_pos n).ne'
  field_simp [ne]
  ring
end AiresKahnFamily
#print axioms AiresKahnFamily.weighting_shift
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
def flipAfter (n q x : ℕ) : ℕ := if x≤q then x else q+2*m n+1-x
theorem flipAfter_mem (n q x : ℕ) (hx : x∈slot n) : flipAfter n q x∈slot n := by
  have h := Finset.mem_Icc.mp hx
  apply Finset.mem_Icc.mpr
  unfold flipAfter
  split <;> omega
theorem flipAfter_above (n q x : ℕ) (hx : x∈slot n) (h : q<x) :
    q < flipAfter n q x := by
  have H := (Finset.mem_Icc.mp hx).2
  unfold flipAfter
  rw [ite_eq_right (not_le.mpr h)]
  omega
theorem flipAfter_twice (n q x : ℕ) (hx : x∈slot n) :
    flipAfter n q (flipAfter n q x)=x := by
  rcases le_or_gt x q with h|h
  · simp [flipAfter,h]
  · have u := flipAfter_above n q x hx h
    have H := (Finset.mem_Icc.mp hx).2
    unfold flipAfter at *
    rw [ite_eq_right (not_le.mpr h),ite_eq_right (not_le.mpr (by
      rw [ite_eq_right (not_le.mpr h)] at u
      exact u))]
    omega
def flipped (n q : ℕ) : Full n ≃ Full n :=
  relabelEquiv (flipAfter n q) (flipAfter n q) (flipAfter_mem n q) (flipAfter_mem n q)
    (flipAfter_twice n q) (flipAfter_twice n q)
theorem flipped_comp {n : ℕ} (q : ℕ) (p : Full n) :
    flipped n q (comp p)=comp (flipped n q p) := by
  apply Subtype.ext
  change (slot n \ p.val).image (flipAfter n q) = slot n \ p.val.image (flipAfter n q)
  ext x
  simp only [Finset.mem_image,Finset.mem_sdiff]
  constructor
  · rintro ⟨y,⟨hy,hp⟩,rfl⟩
    refine ⟨flipAfter_mem n q y hy,?_⟩
    rintro ⟨z,hz,heq⟩
    have H := congrArg (flipAfter n q) heq
    rw [flipAfter_twice n q z (selSub p hz),flipAfter_twice n q y hy] at H
    exact hp (H ▸ hz)
  · rintro ⟨hx,hn⟩
    refine ⟨flipAfter n q x,⟨flipAfter_mem n q x hx,?_⟩,flipAfter_twice n q x hx⟩
    intro hm
    exact hn ⟨_,hm,flipAfter_twice n q x hx⟩
theorem flipAfter_inj (n q : ℕ) : Set.InjOn (flipAfter n q) ↑(slot n) := by
  intro a ha b hb h
  exact (flipAfter_twice n q a ha).symm.trans
    ((congrArg (flipAfter n q) h).trans (flipAfter_twice n q b hb))
theorem flipped_low_rank {n : ℕ} (q : ℕ) (p : Full n) (i : Fin (m n))
    (h : srank p i≤q) :
    srank (flipped n q p) i=srank p i := by
  let x := srank p i
  have h₁ := (srank_eq_iff p i x).1 rfl
  have hh : flipAfter n q x=x := ite_eq_left h
  refine (srank_eq_iff _ _ _).2 ⟨Finset.mem_image.mpr ⟨x,h₁.1,hh⟩,?_⟩
  change (before (p.val.image (flipAfter n q)) x).card=i.val
  nth_rw 1 [←hh]
  rw [before_image,Finset.card_image_of_injOn]
  · exact h₁.2
  · intro a ha b hb he
    exact flipAfter_inj n q (selSub p (Finset.mem_filter.mp ha).1)
      (selSub p (Finset.mem_filter.mp hb).1) he
  · intro a ha
    rw [hh]
    by_cases H : a≤q
    · rw [show flipAfter n q a=a from ite_eq_left H]
    · have H' := flipAfter_above n q a (selSub p ha) (by omega)
      have h' : x≤q := h
      omega
theorem flipped_twice {n : ℕ} (q : ℕ) (p : Full n) :
    flipped n q (flipped n q p)=p := by
  apply Subtype.ext
  change (p.val.image (flipAfter n q)).image (flipAfter n q)=p.val
  rw [Finset.image_image]
  trans p.val.image id
  · exact Finset.image_congr (fun x hx => flipAfter_twice n q x (selSub p hx))
  · exact Finset.image_id
def suffixReverse {n : ℕ} (p : Deleted n) : Deleted n := by
  let q := bMid p.val
  have h : aMid p.val<q := p.property
  refine ⟨flipped n q p.val,?_⟩
  change srank (flipped n q p.val) (mid n) <
    srank (comp (flipped n q p.val)) (mid n)
  rw [←flipped_comp,flipped_low_rank _ _ _ (by exact h.le),
       flipped_low_rank _ _ _ (by exact le_rfl)]
  exact h
theorem suffixReverse_a {n : ℕ} (p : Deleted n) :
    aMid (suffixReverse p).val=aMid p.val :=
  flipped_low_rank _ _ _ p.property.le
theorem suffixReverse_b {n : ℕ} (p : Deleted n) :
    bMid (suffixReverse p).val=bMid p.val := by
  change srank (comp (flipped n (bMid p.val) p.val)) (mid n)=_
  rw [←flipped_comp]
  exact flipped_low_rank _ _ _ le_rfl
theorem suffixReverse_involution {n : ℕ} : Function.Involutive (@suffixReverse n) := by
  intro p
  apply Subtype.ext
  change flipped n (bMid (suffixReverse p).val) (flipped n (bMid p.val) p.val)=p.val
  rw [suffixReverse_b,flipped_twice]
def suffixReverseEquiv (n : ℕ) : Deleted n ≃ Deleted n :=
  ⟨suffixReverse,suffixReverse,suffixReverse_involution,suffixReverse_involution⟩
end AiresKahnFamily
#print axioms AiresKahnFamily.suffixReverse_involution
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
theorem flipped_target_rank {n : ℕ} (p : Deleted n) (j : Fin (m n))
    (hj : mid n<j) (hmed : 2*j.val=3*n+1) :
    bRank j (suffixReverse p)+bRank j p=bMid p.val+2*m n+1 := by
  let b := comp p.val
  let q := bMid p.val
  let x := bRank j p
  have hxq : q<x := (indexedRank_mono b.val (selCard b)) hj
  have hq := (srank_eq_iff b (mid n) q).1 rfl
  have hx := (srank_eq_iff b j x).1 rfl
  have hx_slot := selSub b hx.1
  have hx_le := (Finset.mem_Icc.mp hx_slot).2
  have fxq := flipAfter_above n q x hx_slot hxq
  have hs : srank (flipped n q b) j = flipAfter n q x := by
    refine (srank_eq_iff _ _ _).2 ⟨Finset.mem_image.mpr ⟨x,hx.1,rfl⟩,?_⟩
    change (before (b.val.image (flipAfter n q)) (flipAfter n q x)).card=j.val
    have H : before (b.val.image (flipAfter n q)) (flipAfter n q x) =
        (before b.val (q+1) ∪ after b.val x).image (flipAfter n q) := by
      ext a
      simp only [before,after,Finset.mem_filter,Finset.mem_image,Finset.mem_union]
      have H' (r : ℕ) (hr : r∈b.val) :
          flipAfter n q r<flipAfter n q x ↔ r<q+1 ∨ x<r := by
        by_cases hh : r≤q
        · rw [show flipAfter n q r=r from ite_eq_left hh]
          omega
        · have w := (Finset.mem_Icc.mp (selSub b hr)).2
          unfold flipAfter
          rw [ite_eq_right hh,ite_eq_right (not_le.mpr hxq)]
          omega
      constructor
      · rintro ⟨⟨r,hr,rfl⟩,ha⟩
        refine ⟨r,?_,rfl⟩
        rcases (H' r hr).1 ha with h|h
        · exact Or.inl ⟨hr,h⟩
        · exact Or.inr ⟨hr,h⟩
      · rintro ⟨r,hr,rfl⟩
        rcases hr with ⟨hr,h⟩|⟨hr,h⟩
        · exact ⟨⟨r,hr,rfl⟩,(H' r hr).2 (Or.inl h)⟩
        · exact ⟨⟨r,hr,rfl⟩,(H' r hr).2 (Or.inr h)⟩
    have hdis : Disjoint (before b.val (q+1)) (after b.val x) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      have h := (Finset.mem_filter.mp ha).2
      have H := (Finset.mem_filter.mp hb).2
      omega
    have hsub : before b.val (q+1) ∪ after b.val x ⊆ slot n :=
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)).trans (selSub b)
    rw [H,Finset.card_image_of_injOn ((flipAfter_inj n q).mono (fun _ h => hsub h)),
      Finset.card_union_of_disjoint hdis,before_succ _ _ hq.1,
      Finset.card_insert_of_notMem (before_no_self _ _),hq.2,after_card_of_rank b j x rfl]
    change n+1+(m n-1-j.val)=j.val
    have hj0:=j.isLt
    dsimp [m] at *
    omega
  have U : bRank j (suffixReverse p)=flipAfter n q x := by
    change srank (comp (flipped n q p.val)) j=_
    rw [←flipped_comp]
    exact hs
  rw [U]
  unfold flipAfter
  rw [ite_eq_right (not_le.mpr hxq)]
  change q+2*m n+1-x+x=q+2*m n+1
  omega
end AiresKahnFamily
#print axioms AiresKahnFamily.flipped_target_rank
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
open scoped BigOperators
theorem covar_linear {ι : Type} [Fintype ι] (w f g h : ι → ℚ) (c : ℚ) :
    covar w (fun i=>c*f i-g i) h = c*covar w f h - covar w g h := by
  unfold covar
  have H : (fun i => (c*f i-g i)*h i) = fun i => c*(f i*h i)-g i*h i := by
    funext i
    ring
  rw [H,wmean_sub,wmean_sub,wmean_mul,wmean_mul]
  ring
theorem mid_covariance (n : ℕ) :
    covar (uniform (Deleted n)) (fun p => (bMid p.val:ℚ)) gap =
      wvar (uniform (Deleted n)) gap/2 := by
  have := deleted_nonempty n
  let a : Deleted n → ℚ := fun p => aMid p.val
  let b : Deleted n → ℚ := fun p => bMid p.val
  apply covariance_rank _ a b gap (fun _=>rfl)
  apply covariance_reflected _ _ _ ((2*m n+1:ℕ):ℚ) (swapReverseEquiv n)
      (uniform_sum _) (fun _=>rfl)
  · intro p
    change (aMid (swapReverse p).val:ℚ)+(bMid (swapReverse p).val:ℚ)=_
    rw [swapReverse_a,swapReverse_b]
    have ha := (Finset.mem_Icc.mp (srank_in p.val (mid n))).2
    have hb := (Finset.mem_Icc.mp (srank_in (comp p.val) (mid n))).2
    change aMid p.val≤2*m n at ha
    change bMid p.val≤2*m n at hb
    unfold reflectPos
    rw [Nat.cast_sub (show _ ≤ 2*m n+1 by omega),
        Nat.cast_sub (show _ ≤ 2*m n+1 by omega)]
    dsimp [a,b]
    ring
  · intro p
    change gap (swapReverse p) = gap p
    unfold gap
    rw [swapReverse_a,swapReverse_b]
    have ha := (Finset.mem_Icc.mp (srank_in p.val (mid n))).2
    have hb := (Finset.mem_Icc.mp (srank_in (comp p.val) (mid n))).2
    change aMid p.val≤2*m n at ha
    change bMid p.val≤2*m n at hb
    unfold reflectPos
    rw [Nat.cast_sub (show _ ≤ 2*m n+1 by omega),
        Nat.cast_sub (show _ ≤ 2*m n+1 by omega)]
    ring
theorem target_covariance {n : ℕ} (j : Fin (m n))
    (hj : mid n<j) (hmed : 2*j.val=3*n+1) :
    covar (uniform (Deleted n)) (fun p => (bRank j p:ℚ)) gap =
      wvar (uniform (Deleted n)) gap/4 := by
  have := deleted_nonempty n
  have H : covar (uniform (Deleted n))
      (fun p => 2*(bRank j p:ℚ)-(bMid p.val:ℚ)) gap=0 := by
    apply covariance_reflected _ _ _ ((2*m n+1:ℕ):ℚ) (suffixReverseEquiv n)
      (uniform_sum _) (fun _=>rfl)
    · intro p
      change 2*(bRank j (suffixReverse p):ℚ)-(bMid (suffixReverse p).val:ℚ)=_
      rw [suffixReverse_b]
      have hp := congrArg (fun x : ℕ=> (x:ℚ)) (flipped_target_rank p j hj hmed)
      push_cast at hp ⊢
      linarith
    · intro p
      change gap (suffixReverse p)=gap p
      unfold gap
      rw [suffixReverse_b,suffixReverse_a]
  rw [covar_linear,mid_covariance] at H
  linarith
theorem raw_shift_formula {n : ℕ} (j : Fin (m n))
    (hj : mid n<j) (hmed : 2*j.val=3*n+1) :
    wmean (uniform (Marked n)) (fun z => (markedBRank j z:ℚ)) -
    wmean (uniform (Deleted n)) (fun p => (bRank j p:ℚ)) =
      1+wvar (uniform (Deleted n)) gap/(4*wmean (uniform (Deleted n)) gap) := by
  rw [weighting_shift j hj.le,target_covariance j hj hmed]
  ring
theorem raw_shift_unbounded (h : ℕ) (hh : 1≤h) :
    ∃ n, ∃ j : Fin (m n), n+1=4*h^2 ∧ mid n<j ∧ 2*j.val=3*n+1 ∧
      1+(h:ℚ)/320 ≤
        wmean (uniform (Marked n)) (fun z => (markedBRank j z:ℚ)) -
        wmean (uniform (Deleted n)) (fun p => (bRank j p:ℚ)) := by
  let r := 2*h^2
  have hr : 1≤r := by dsimp [r]; nlinarith
  let n := 2*r-1
  have hN : n+1=4*h^2 := by
    calc
      n+1=2*r := by dsimp [n]; omega
      _=4*h^2 := by dsimp [r]; ring
  let j : Fin (m n) := ⟨3*r-1,by dsimp [n,m]; omega⟩
  have hj : mid n<j := by change n<3*r-1; dsimp [n]; omega
  have hmed : 2*j.val=3*n+1 := by change 2*(3*r-1)=3*n+1; dsimp [n]; omega
  refine ⟨n,j,hN,hj,hmed,?_⟩
  rw [raw_shift_formula j hj hmed]
  exact gap_bound_scale n h hh hN
end AiresKahnFamily
#print axioms AiresKahnFamily.raw_shift_unbounded
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
abbrev hole (n x : ℕ) := (interval (2*m n+1)).erase x
def removeRank (x r : ℕ) := if r<x then r else r-1
theorem insertRank_strict (x : ℕ) : StrictMono (insertRank x) := by
  intro a b h
  unfold insertRank
  split <;> (try split) <;> omega
theorem insertRank_mem {n x : ℕ} (_h : 1≤x ∧ x≤2*m n+1)
    (a : ℕ) (ha : a∈slot n) : insertRank x a ∈ hole n x := by
  have H := Finset.mem_Icc.mp ha
  apply Finset.mem_erase.mpr
  unfold insertRank
  split <;> exact ⟨by omega,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
theorem removeRank_mem {n x : ℕ} (h : 1≤x ∧ x≤2*m n+1)
    (a : ℕ) (ha : a∈hole n x) : removeRank x a ∈ slot n := by
  have H := Finset.mem_Icc.mp (Finset.mem_erase.mp ha).2
  have hn := (Finset.mem_erase.mp ha).1
  apply Finset.mem_Icc.mpr
  unfold removeRank
  split <;> exact ⟨by omega,by omega⟩
theorem remove_insert (x a : ℕ) : removeRank x (insertRank x a) = a := by
  unfold insertRank removeRank
  split <;> (try split) <;> omega
theorem insert_remove (x a : ℕ) (ha : a≠x) :
    insertRank x (removeRank x a) = a := by
  unfold insertRank removeRank
  split <;> (try split) <;> omega
theorem hole_card {n x : ℕ} (h : 1≤x ∧ x≤2*m n+1) :
    (hole n x).card=2*m n := by
  unfold hole
  rw [Finset.card_erase_of_mem (Finset.mem_Icc.mpr h),Nat.card_Icc]
  omega
def holeComp {n x : ℕ} (h : 1≤x ∧ x≤2*m n+1)
    (p : Sel (hole n x) (m n)) : Sel (hole n x) (m n) :=
  ⟨hole n x \ p.val,Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset,by
    rw [Finset.card_sdiff_of_subset (selSub p),hole_card h,selCard p]
    omega⟩⟩
def holeEquiv {n x : ℕ} (h : 1≤x ∧ x≤2*m n+1) : Full n ≃ Sel (hole n x) (m n) :=
  relabelEquiv (insertRank x) (removeRank x) (insertRank_mem h) (removeRank_mem h)
    (fun a _ => remove_insert x a) (fun a ha => insert_remove x a (Finset.mem_erase.mp ha).1)
theorem holeEquiv_rank {n x : ℕ} (h : 1≤x ∧ x≤2*m n+1)
    (p : Full n) (i : Fin (m n)) :
    srank (holeEquiv h p) i=insertRank x (srank p i) := by
  have H := rank_relabel _ (insertRank_mem h) (insertRank_strict x).injective.injOn
    (fun a _ b _ => (insertRank_strict x).lt_iff_lt) p i
  exact H
theorem holeEquiv_comp {n x : ℕ} (h : 1≤x ∧ x≤2*m n+1) (p : Full n) :
    holeEquiv h (comp p)=holeComp h (holeEquiv h p) := by
  apply Subtype.ext
  change (slot n \ p.val).image (insertRank x) = hole n x \ p.val.image (insertRank x)
  ext a
  simp only [Finset.mem_image,Finset.mem_sdiff]
  constructor
  · rintro ⟨r,⟨hr,hp⟩,rfl⟩
    refine ⟨insertRank_mem h r hr,?_⟩
    rintro ⟨s,hs,he⟩
    exact hp ((insertRank_strict x).injective he ▸ hs)
  · rintro ⟨ha,hn⟩
    have ea := insert_remove x a (Finset.mem_erase.mp ha).1
    refine ⟨removeRank x a,⟨removeRank_mem h a ha,?_⟩,ea⟩
    intro hm
    exact hn ⟨_,hm,ea⟩
end AiresKahnFamily
#print axioms AiresKahnFamily.holeEquiv_comp
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
open scoped BigOperators
abbrev MSlot (n : ℕ) := Fin (2*m n+1)
theorem mslot_bounds {n : ℕ} (x : MSlot n) : 1≤x.val+1 ∧ x.val+1≤2*m n+1 := by
  have h := x.isLt
  omega
abbrev StandardMarked (n : ℕ) :=
  Σ x : MSlot n, {p : Sel (hole n (x.val+1)) (m n) //
    srank p (mid n) < x.val+1 ∧
      x.val+1 < srank (holeComp (mslot_bounds x) p) (mid n)}
theorem marker_slot_bounds {n : ℕ} (z : Marked n) :
    1≤ marker z ∧ marker z≤2*m n+1 := by
  have H := marker_bounds z
  have S := (Finset.mem_Icc.mp (srank_in (comp z.1.val) (mid n))).2
  change bMid z.1.val≤2*m n at S
  omega
def markerSlot {n : ℕ} (z : Marked n) : MSlot n := ⟨marker z-1,by
  have h := marker_slot_bounds z
  omega⟩
theorem markerSlot_val {n : ℕ} (z : Marked n) :
    (markerSlot z).val+1=marker z := by
  have H := (marker_slot_bounds z).1
  change marker z-1+1=marker z
  omega
theorem insertRank_before {x a : ℕ} : insertRank x a<x ↔ a<x := by
  unfold insertRank
  split <;> omega
theorem insertRank_after {x a : ℕ} : x< insertRank x a ↔ x≤a := by
  unfold insertRank
  split <;> omega
def toStandardMarked {n : ℕ} (z : Marked n) : StandardMarked n := by
  let x := markerSlot z
  let p := holeEquiv (mslot_bounds x) z.1.val
  refine ⟨x,⟨p,?_⟩⟩
  dsimp [p]
  rw [←holeEquiv_comp,holeEquiv_rank,holeEquiv_rank,insertRank_before,insertRank_after]
  change aMid z.1.val < (markerSlot z).val+1 ∧
    (markerSlot z).val+1 ≤ bMid z.1.val
  rw [markerSlot_val]
  exact marker_bounds z
theorem standardMarked_rank {n : ℕ} (z : Marked n) (j : Fin (m n)) :
    srank (holeComp (mslot_bounds (toStandardMarked z).1) (toStandardMarked z).2.val) j =
      markedBRank j z := by
  change srank (holeComp (mslot_bounds (markerSlot z))
    (holeEquiv (mslot_bounds (markerSlot z)) z.1.val)) j=_
  rw [←holeEquiv_comp,holeEquiv_rank,markerSlot_val]
  rfl
theorem standardMarked_injective {n : ℕ} : Function.Injective (@toStandardMarked n) := by
  intro z z' h
  have hx := congrArg Sigma.fst h
  change markerSlot z=markerSlot z' at hx
  have hm : marker z=marker z' := by rw [←markerSlot_val z,←markerSlot_val z',hx]
  have hp : z.1=z'.1 := by
    apply Subtype.ext
    have hA := congrArg (fun a : StandardMarked n => a.2.val.val) h
    change (holeEquiv (mslot_bounds (markerSlot z)) z.1.val).val =
      (holeEquiv (mslot_bounds (markerSlot z')) z'.1.val).val at hA
    rw [hx] at hA
    exact (holeEquiv (mslot_bounds (markerSlot z'))).injective (Subtype.ext hA)
  apply Sigma.ext_iff.2
  refine ⟨hp,?_⟩
  rcases z with ⟨p,i⟩
  rcases z' with ⟨p',i'⟩
  change p=p' at hp
  subst p'
  change aMid p.val+i.val+1=aMid p.val+i'.val+1 at hm
  change HEq i i'
  have eq : i=i' := Fin.ext (by omega)
  exact heq_of_eq eq
theorem standardMarked_surjective {n : ℕ} : Function.Surjective (@toStandardMarked n) := by
  intro z
  rcases z with ⟨x,u⟩
  let p := (holeEquiv (mslot_bounds x)).symm u.val
  have hp : holeEquiv (mslot_bounds x) p=u.val := Equiv.apply_symm_apply _ _
  have H := u.property
  rw [←hp,←holeEquiv_comp,holeEquiv_rank,holeEquiv_rank,insertRank_before,insertRank_after] at H
  change aMid p < x.val+1 ∧ x.val+1≤ bMid p at H
  let d : Deleted n := ⟨p,by exact H.1.trans_le H.2⟩
  let k : Fin (gapNat d) := ⟨x.val+1-aMid p-1,by
      change x.val+1-aMid p-1< bMid p-aMid p
      omega⟩
  let e : Marked n := ⟨d,k⟩
  have hm : marker e=x.val+1 := by
    change aMid p+(x.val+1-aMid p-1)+1=x.val+1
    omega
  have hx : markerSlot e=x := by
    apply Fin.ext
    change marker e-1=x.val
    omega
  have hx' : (toStandardMarked e).1=x := hx
  refine ⟨e,?_⟩
  apply Sigma.ext_iff.2
  refine ⟨hx',?_⟩
  generalize he : toStandardMarked e = y
  have hy : y.1=x := he ▸ hx'
  have hp' : y.2.val.val=u.val.val := by
    rw [←he]
    change (holeEquiv (mslot_bounds (markerSlot e)) p).val=u.val.val
    rw [hx,hp]
  rcases y with ⟨y,Y⟩
  change y=x at hy
  subst y
  exact heq_of_eq (Subtype.ext (Subtype.ext hp'))
noncomputable def standardMarkedEquiv (n : ℕ) : Marked n ≃ StandardMarked n :=
  Equiv.ofBijective _ ⟨standardMarked_injective,standardMarked_surjective⟩
end AiresKahnFamily
#print axioms AiresKahnFamily.standardMarked_rank
#print axioms AiresKahnFamily.standardMarkedEquiv
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
inductive Vertex (n : ℕ) where
  | a : Fin (m n) → Vertex n
  | x : Vertex n
  | b : Fin (m n) → Vertex n
deriving DecidableEq
def ltV {n : ℕ} : Vertex n → Vertex n → Prop
  | .a i, .a j => i.val<j.val
  | .b i, .b j => i.val<j.val
  | .a i, .x => i.val≤n
  | .x, .b j => n≤j.val
  | .a i, .b j => i.val≤n ∧ n≤j.val
  | _, _ => False
theorem ltV_irreflexive (n : ℕ) : ∀ a : Vertex n, ¬ltV a a := by
  intro a
  cases a <;> simp [ltV]
theorem ltV_transitive (n : ℕ) : ∀ a b c : Vertex n, ltV a b → ltV b c → ltV a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp only [ltV] at * <;> omega
def cover {n : ℕ} (a b : Vertex n) : Prop :=
  ltV a b ∧ ∀ c, ltV a c → ¬ltV c b
def coverAdj {n : ℕ} (a b : Vertex n) : Prop := cover a b ∨ cover b a
def level {n : ℕ} : Vertex n → ℕ
  | .a i => i.val
  | .x => n+1
  | .b i => i.val+2
theorem cover_step {n : ℕ} {a b : Vertex n} (h : cover a b) :
    level b=level a+1 := by
  rcases h with ⟨h,hgap⟩
  cases a <;> cases b <;> simp only [ltV,level] at h ⊢ <;> try contradiction
  · rename_i i j
    by_contra! bad
    let k : Fin (m n) := ⟨i.val+1,by have H:=j.isLt; omega⟩
    apply hgap (.a k) <;> change _ < _ <;> dsimp [k] <;> omega
  · rename_i i
    by_contra! bad
    apply hgap (.a (mid n))
    · change i.val<n
      omega
    · change n≤n
      exact le_rfl
  · rename_i i j
    exact False.elim (hgap .x h.1 h.2)
  · rename_i j
    by_contra! bad
    apply hgap (.b (mid n))
    · change n≤n
      exact le_rfl
    · change n<j.val
      omega
  · rename_i i j
    by_contra! bad
    let k : Fin (m n) := ⟨i.val+1,by have H:=j.isLt; omega⟩
    apply hgap (.b k) <;> change _ < _ <;> dsimp [k] <;> omega
theorem step_x_mid (n : ℕ) : cover (.x : Vertex n) (.b (mid n)) := by
  refine ⟨le_rfl,?_⟩
  intro c hc h
  cases c <;> simp only [ltV,mid] at *
  all_goals omega
theorem step_bb {n : ℕ} {i j : Fin (m n)} (h : j.val=i.val+1) :
    cover (Vertex.b i) (Vertex.b j) := by
  refine ⟨by change i.val<j.val; omega,?_⟩
  intro c hc he
  cases c <;> simp only [ltV] at *
  all_goals omega
inductive Walk {n : ℕ} (R : Vertex n → Vertex n → Prop) : ℕ → Vertex n → Vertex n → Prop
  | nil (a) : Walk R 0 a a
  | cons {k a b c} : R a b → Walk R k b c → Walk R (k+1) a c
theorem cover_walk_lower {n k : ℕ} {a b : Vertex n} (h : Walk coverAdj k a b) :
    level b ≤ level a+k := by
  induction h with
  | nil => simp
  | @cons k a c b hs _ ih =>
    rcases hs with hs|hs <;> have H := cover_step hs <;> omega
theorem covers_to_adj {n k : ℕ} {a b : Vertex n} (h : Walk cover k a b) :
    Walk coverAdj k a b := by
  induction h with
  | nil => exact .nil _
  | cons e _ t => exact .cons (Or.inl e) t
theorem walk_b {n : ℕ} (i j : Fin (m n)) (h : i.val≤j.val) :
    Walk cover (j.val-i.val) (.b i) (.b j) := by
  generalize H : j.val-i.val = d
  induction d generalizing i with
  | zero =>
    have eq : i=j := Fin.ext (by omega)
    subst i
    exact .nil _
  | succ d ih =>
    let k : Fin (m n) := ⟨i.val+1,by have J:=j.isLt; omega⟩
    have hk : k.val=i.val+1 := rfl
    have X := ih k (by omega) (by omega)
    exact .cons (step_bb hk) X
theorem exact_x_b_distance {n : ℕ} (j : Fin (m n)) (hj : mid n≤j) :
    Walk cover (j.val-n+1) (.x : Vertex n) (.b j) ∧
      ∀ k, Walk coverAdj k (.x : Vertex n) (.b j) → j.val-n+1≤k := by
  have h : n≤j.val := hj
  constructor
  · exact .cons (step_x_mid n) (walk_b (mid n) j h)
  · intro k w
    have H := cover_walk_lower w
    change j.val+2≤n+1+k at H
    omega
end AiresKahnFamily
#print axioms AiresKahnFamily.exact_x_b_distance
namespace AiresKahnFamily
open AiresKahnSubset AiresKahnLocal
def standardRank {n : ℕ} (z : StandardMarked n) : Vertex n → ℕ
  | .a i => srank z.2.val i
  | .x => z.1.val+1
  | .b i => srank (holeComp (mslot_bounds z.1) z.2.val) i
theorem standard_order {n : ℕ} (z : StandardMarked n) (a b : Vertex n)
    (h : ltV a b) : standardRank z a<standardRank z b := by
  have hA := indexedRank_mono z.2.val.val (selCard z.2.val)
  have hB := indexedRank_mono (holeComp (mslot_bounds z.1) z.2.val).val
    (selCard (holeComp (mslot_bounds z.1) z.2.val))
  have ha := z.2.property.1
  have hb := z.2.property.2
  cases a <;> cases b <;> simp only [ltV,standardRank] at h ⊢ <;> try contradiction
  · exact hA h
  · exact (hA.monotone h).trans_lt ha
  · exact ((hA.monotone h.1).trans_lt ha).trans (hb.trans_le (hB.monotone h.2))
  · exact hb.trans_le (hB.monotone h)
  · exact hB h
def deletionRank {n : ℕ} (z : Deleted n) : Vertex n → ℕ
  | .a i => srank z.val i
  | .x => 0
  | .b i => srank (comp z.val) i
theorem deletion_order {n : ℕ} (z : Deleted n) (a b : Vertex n)
    (ha : a ≠ .x) (hb : b ≠ .x) (h : ltV a b) :
    deletionRank z a<deletionRank z b := by
  have hA := indexedRank_mono z.val.val (selCard z.val)
  have hB := indexedRank_mono (comp z.val).val (selCard (comp z.val))
  have hmid : aMid z.val<bMid z.val := z.property
  cases a <;> cases b <;> simp only [ltV,deletionRank] at h ⊢ <;> try contradiction
  · exact hA h
  · exact ((hA.monotone h.1).trans_lt hmid).trans_le (hB.monotone h.2)
  · exact hB h
def standardShift {n : ℕ} (j : Fin (m n)) : ℚ :=
    wmean (uniform (StandardMarked n)) (fun z => (standardRank z (.b j):ℚ)) -
      wmean (uniform (Deleted n)) (fun p => (deletionRank p (.b j):ℚ))
theorem standardShift_eq {n : ℕ} (j : Fin (m n)) :
    standardShift j =
      wmean (uniform (Marked n)) (fun z => (markedBRank j z:ℚ)) -
      wmean (uniform (Deleted n)) (fun p => (bRank j p:ℚ)) := by
  unfold standardShift
  rw [← uniform_transport _ (standardMarkedEquiv n)]
  congr 1
  congr 1
  funext z
  exact_mod_cast standardMarked_rank z j
theorem counterexamples_12_6_ab (C : ℚ) :
    ∃ n, ∃ j : Fin (m n), ∃ d : ℕ,
      2*m n+1 ≤ 8*d ∧ Walk cover d (.x : Vertex n) (.b j) ∧
      (∀ k, Walk coverAdj k (.x : Vertex n) (.b j) → d≤k) ∧
      C < standardShift j := by
  obtain ⟨k,hk⟩ := exists_nat_gt (320*C)
  have h1 : 1≤k+1 := by omega
  obtain ⟨n,j,_,hj,hm,hshift⟩ := raw_shift_unbounded (k+1) h1
  rw [←standardShift_eq] at hshift
  have H := exact_x_b_distance j hj.le
  refine ⟨n,j,j.val-n+1,?_,H.1,H.2,?_⟩
  · dsimp [m]
    omega
  · push_cast at hshift
    linarith
end AiresKahnFamily
#print axioms AiresKahnFamily.standard_order
#print axioms AiresKahnFamily.deletion_order
#print axioms AiresKahnFamily.counterexamples_12_6_ab
