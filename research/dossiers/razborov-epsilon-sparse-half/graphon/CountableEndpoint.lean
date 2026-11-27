import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace SparseHalfCountableEndpoint
variable {ι : Type*}

/-- A single strictly positive gap survives taking the full summable limit. -/
theorem rigid_of_summable_gap (f g : ι → ℝ) (hg : Summable g)
    (hf0 : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i)
    (h : (∑' i, g i) ≤ ∑' i, f i) : ∀ i, f i = g i := by
  have hf := Summable.of_nonneg_of_le hf0 hfg hg
  intro i
  by_contra ne
  have pos : 0 < g i - f i := sub_pos.mpr (lt_of_le_of_ne (hfg i) ne)
  have H := (hg.sub hf).tsum_pos (fun j => sub_nonneg.mpr (hfg j)) i pos
  rw [hg.tsum_sub hf] at H
  linarith

/-- Localization of positive price thresholds, with no finite index premise. -/
theorem finite_threshold (p : ι → ℝ) (hp : Summable p) {θ : ℝ} (hθ : 0 < θ) :
    {i | θ ≤ p i}.Finite := by
  have H := hp.tendsto_cofinite_zero.eventually (gt_mem_nhds hθ)
  simpa only [Filter.eventually_cofinite, not_lt] using H

private theorem saturate (p q f : ι → ℝ) (c h : ℝ)
    (hs : Summable (fun i => p i+q i))
    (hc : 0 < c) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ f i)
    (hfg : ∀ i, f i ≤ c*(p i+q i))
    (hmass : (∑' i, (p i+q i)) + h = 6)
    (hbudget : 6*c ≤ ∑' i, f i) :
    h=0 ∧ ∀ i, f i = c*(p i+q i) := by
  have hg := hs.mul_left c
  have hfs := Summable.of_nonneg_of_le hf hfg hg
  have total := Summable.tsum_le_tsum hfg hfs hg
  rw [hs.tsum_mul_left c] at total
  have hz : h=0 := by nlinarith [mul_nonneg hc.le hh]
  refine ⟨hz, rigid_of_summable_gap f _ hg hf hfg ?_⟩
  rw [hs.tsum_mul_left c]
  rw [hz,add_zero] at hmass
  rw [hmass]
  simpa only [mul_comm] using hbudget

/-- All nonzero pairs are the same positive pair; the exact mass forces
a finite support and determines its cardinality. -/
theorem exact_support (p q : ι → ℝ) {P Q h : ℝ}
    (hP : 0<P) (hQ : 0≤Q) (hs : Summable (fun i => p i+q i))
    (pairs : ∀ i, (p i=0 ∧ q i=0) ∨ (p i=P ∧ q i=Q))
    (total : (∑' i, (p i+q i))+h=6) :
    ∃ s : Finset ι, (∀ i, i∈s ↔ p i=P ∧ q i=Q) ∧
      (∀ i, i∉s → p i=0 ∧ q i=0) ∧ (s.card:ℝ)*(P+Q)+h=6 := by
  classical
  let s := (finite_threshold _ hs (add_pos_of_pos_of_nonneg hP hQ)).toFinset
  have mem (i : ι) : i∈s ↔ p i=P ∧ q i=Q := by
    change _ ∈ Set.Finite.toFinset _ ↔ _
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rcases pairs i with ⟨pi,qi⟩ | ⟨pi,qi⟩
    · rw [pi,qi]
      have ht : ¬ P+Q≤0+0 := by linarith
      simp [(ne_of_gt hP).symm, add_pos_of_pos_of_nonneg hP hQ]
    · simp [pi,qi]
  have outside (i : ι) (hi : i∉s) : p i=0 ∧ q i=0 :=
    (pairs i).resolve_right (fun r => hi ((mem i).2 r))
  refine ⟨s, mem, outside, ?_⟩
  rw [tsum_eq_sum (s:=s) (fun i hi => by simp [(outside i hi).1,(outside i hi).2])] at total
  rw [←total]
  congr 1
  rw [←nsmul_eq_mul, ←Finset.sum_const]
  exact Finset.sum_congr rfl fun i hi => by rw [((mem i).1 hi).1,((mem i).1 hi).2]

theorem priceOne (p q : ι → ℝ) (h : ℝ)
    (hs : Summable (fun i => p i+q i))
    (hq : ∀ i, 0≤q i ∧ q i≤1) (hqp : ∀ i, q i≤p i)
    (hh : 0≤h) (hmass : (∑' i, (p i+q i))+h=6)
    (he : 3≤∑' i, q i*min 1 (p i)) :
    h=0 ∧ ∃ s : Finset ι, s.card=3 ∧
      (∀ i∈s, p i=1 ∧ q i=1) ∧ (∀ i∉s, p i=0 ∧ q i=0) := by
  have pos i : 0≤p i := (hq i).1.trans (hqp i)
  have low i : 0≤q i * min 1 (p i) := mul_nonneg (hq i).1 (le_min (by norm_num) (pos i))
  have mid i : q i*min 1 (p i)≤q i := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (p i)) (hq i).1
  have bound i : q i*min 1 (p i)≤(1/2)*(p i+q i) := by linarith [mid i,hqp i]
  obtain ⟨hz, eq⟩ := saturate p q (fun i => q i*min 1 (p i)) (1/2) h
    hs (by norm_num) hh low bound hmass (by norm_num; exact he)
  have pairs i : (p i=0 ∧ q i=0) ∨ (p i=1 ∧ q i=1) := by
    have pq : p i=q i := by linarith [eq i,mid i,hqp i]
    have m := eq i
    rw [pq,min_eq_right (hq i).2] at m
    have z : q i*(q i-1)=0 := by nlinarith
    rcases mul_eq_zero.mp z with z | z
    · left; exact ⟨pq.trans z,z⟩
    · right; have q1 := sub_eq_zero.mp z; exact ⟨pq.trans q1,q1⟩
  obtain ⟨s,mem,out,total⟩ := exact_support p q (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)≤1) hs pairs hmass
  have cs : (s.card:ℝ)=3 := by linarith
  exact ⟨hz,s,by exact_mod_cast cs,fun i hi => (mem i).1 hi,out⟩

theorem priceTwo (p q : ι → ℝ) (h : ℝ)
    (hs : Summable (fun i => p i+q i))
    (hp : ∀ i, 0≤p i ∧ p i≤2) (hq : ∀ i, 0≤q i ∧ q i≤1)
    (hh : 0≤h) (hmass : (∑' i, (p i+q i))+h=6)
    (he : 4≤∑' i, p i*q i) :
    h=0 ∧ ∃ s : Finset ι, s.card=2 ∧
      (∀ i∈s, p i=2 ∧ q i=1) ∧ (∀ i∉s, p i=0 ∧ q i=0) := by
  have pos i : 0≤p i*q i := mul_nonneg (hp i).1 (hq i).1
  have gap i : (2/3)*(p i+q i)-p i*q i =
        (2*p i*(1-q i)+q i*(2-p i))/3 := by ring
  have a i := mul_nonneg (hp i).1 (sub_nonneg.mpr (hq i).2)
  have b i := mul_nonneg (hq i).1 (sub_nonneg.mpr (hp i).2)
  have bound i : p i*q i≤(2/3)*(p i+q i) := by linarith [gap i,a i,b i]
  obtain ⟨hz,eq⟩ := saturate p q (fun i => p i*q i) (2/3) h
    hs (by norm_num) hh pos bound hmass (by norm_num; exact he)
  have pairs i : (p i=0 ∧ q i=0) ∨ (p i=2 ∧ q i=1) := by
    have z₁ : p i*(1-q i)=0 := by linarith [gap i,eq i,a i,b i]
    have z₂ : q i*(2-p i)=0 := by linarith [gap i,eq i,a i,b i]
    rcases mul_eq_zero.mp z₁ with z | z
    · left; rw [z,sub_zero] at z₂; exact ⟨z,by linarith⟩
    · right
      have q1 : q i=1 := by linarith
      rw [q1,one_mul] at z₂
      exact ⟨by linarith,q1⟩
  obtain ⟨s,mem,out,total⟩ := exact_support p q (by norm_num : (0:ℝ)<2)
    (by norm_num : (0:ℝ)≤1) hs pairs hmass
  have cs : (s.card:ℝ)=2 := by linarith
  exact ⟨hz,s,by exact_mod_cast cs,fun i hi => (mem i).1 hi,out⟩

#print axioms priceOne
#print axioms priceTwo
end SparseHalfCountableEndpoint
