import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace SparseHalfSaturatedEndpoint
open scoped BigOperators

theorem mid_strict (θ : ℝ) (h1 : 1<θ) (h2 : θ<2) :
    θ+(2-θ)^2<2 := by
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)]

theorem ratio (p q : ℝ) (hp0 : 0≤p) (hp : p≤2) (hq0 : 0≤q) (hq : q≤1) :
    p*q≤(2/3)*(p+q) ∧ (p*q=(2/3)*(p+q) → (p=0 ∧ q=0) ∨ (p=2 ∧ q=1)) := by
  have e : (2/3)*(p+q)-p*q =
      (2*p*(1-q)+q*(2-p))/3 := by ring
  have h1 := mul_nonneg hp0 (sub_nonneg.mpr hq)
  have h2 := mul_nonneg hq0 (sub_nonneg.mpr hp)
  refine ⟨by linarith,?_⟩
  intro hh
  have hx : p*(1-q)=0 := by nlinarith
  have hy : q*(2-p)=0 := by nlinarith
  rcases mul_eq_zero.mp hx with hzero | hone
  · left
    have hz : q=0 := by rw [hzero] at hy; linarith
    exact ⟨hzero,hz⟩
  · right
    have hz : q=1 := by linarith
    rw [hz] at hy
    exact ⟨by linarith,hz⟩

/-- The crude endpoint of the price-two relaxation can occur only at the
exceptional full (2,1)-capacity blocks, or zero blocks. -/
theorem priceTwo {ι : Type*} [Fintype ι] (p q : ι→ℝ) (h : ℝ)
    (hp : ∀ i, 0≤p i ∧ p i≤2) (hq : ∀ i, 0≤q i ∧ q i≤1)
    (hh : 0≤h) (hB : (∑ i, (p i+q i))+h=6)
    (he : 4≤∑ i, p i*q i) :
    h=0 ∧ ∀ i, (p i=0 ∧ q i=0) ∨ (p i=2 ∧ q i=1) := by
  classical
  have hbound : ∀ i, p i*q i≤(2/3)*(p i+q i) :=
    fun i => (ratio (p i) (q i) (hp i).1 (hp i).2 (hq i).1 (hq i).2).1
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hbound i)
  rw [← Finset.mul_sum] at hs
  have hz : h=0 := by linarith
  refine ⟨hz,?_⟩
  intro i
  have hiff := (ratio (p i) (q i) (hp i).1 (hp i).2 (hq i).1 (hq i).2).2
  apply hiff
  by_contra! hn
  have hlt := lt_of_le_of_ne (hbound i) hn
  have hx := Finset.sum_lt_sum (s:=Finset.univ) (fun i _ => hbound i)
    ⟨i,Finset.mem_univ i,hlt⟩
  rw [← Finset.mul_sum] at hx
  linarith

theorem priceOne {ι : Type*} [Fintype ι] (p q : ι→ℝ) (h : ℝ)
    (hq : ∀ i, 0≤q i ∧ q i≤1) (hqp : ∀ i, q i≤p i)
    (hh : 0≤h) (hB : (∑ i, (p i+q i))+h=6)
    (he : 3≤∑ i, q i*min 1 (p i)) :
    h=0 ∧ ∀ i, (p i=0 ∧ q i=0) ∨ (p i=1 ∧ q i=1) := by
  classical
  rw [Finset.sum_add_distrib] at hB
  have h0 : ∀ i, q i*min 1 (p i)≤q i := by
    intro i
    simpa using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (p i)) (hq i).1
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h0 i)
  have hqp' := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hqp i)
  have hz : h=0 := by linarith
  refine ⟨hz,?_⟩
  intro i
  have heq : p i=q i := by
    by_contra! hn
    have hl := lt_of_le_of_ne (hqp i) (Ne.symm hn)
    have hsl := Finset.sum_lt_sum (s:=Finset.univ) (fun i _ => hqp i)
      ⟨i,Finset.mem_univ i,hl⟩
    linarith
  have hpq : q i*min 1 (p i)=q i := by
    by_contra! hn
    have hl := lt_of_le_of_ne (h0 i) hn
    have hsl := Finset.sum_lt_sum (s:=Finset.univ) (fun i _ => h0 i)
      ⟨i,Finset.mem_univ i,hl⟩
    linarith
  rw [heq,min_eq_right (hq i).2] at hpq
  have hprod : q i*(q i-1)=0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hz | h1
  · exact Or.inl ⟨heq.trans hz,hz⟩
  · have h2 : q i=1 := by linarith
    exact Or.inr ⟨heq.trans h2,h2⟩

#print axioms priceOne
#print axioms ratio
#print axioms priceTwo
end SparseHalfSaturatedEndpoint
