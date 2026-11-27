import CountableEndpoint
import LowSmallSide

namespace SparseHalfCountableEndpoint
variable {ι : Type*}

noncomputable def dual (p q : ι → ℝ) (θ : ℝ) :=
  (∑' i, q i*min θ (p i)) - θ

/-- Finite convex packing bounds still apply to every summable bank:
pass through arbitrary finite subfamilies without normalizing away tail mass. -/
theorem interior_bound (p q : ι → ℝ) (θ h : ℝ)
    (hθ : 1≤θ) (hθ' : θ≤2)
    (hp : ∀ i, 0≤p i) (hq : ∀ i, 0≤q i ∧ q i≤1)
    (hs : Summable (fun i => p i+q i))
    (hh : 0≤h) (hmass : (∑' i, (p i+q i))+h=6) :
    dual p q θ≤θ+(2-θ)^2 := by
  open SparseHalfLowSmallSide in
  have rebate (i : ι) :
      q i*min θ (p i)≤g (min (θ+1) (p i+q i)) :=
    block_rebate θ (p i) (q i) hθ (hq i).1 (hq i).2
  have sumQ : Summable (fun i => q i * min θ (p i)) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro i
      exact mul_nonneg (hq i).1 (le_min (by linarith) (hp i))
    · intro i
      exact (mul_le_mul (hq i).2 (min_le_right θ (p i))
        (le_min (by linarith) (hp i)) (by norm_num)).trans
        (by linarith [(hq i).1])
  suffices H : (∑' i, q i*min θ (p i))≤2*θ+(2-θ)^2 by
    unfold dual
    linarith
  apply sumQ.tsum_le_of_sum_le
  intro s
  let v := fun i => min (θ+1) (p i+q i)
  let ys := s.toList.map v
  have hnon i : 0≤p i+q i := add_nonneg (hp i) (hq i).1
  have hy : ∀ x∈ys, 0≤x ∧ x≤θ+1 := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨le_min (by linarith) (hnon i),min_le_left ..⟩
  have hyS : ys.sum≤6 := by
    dsimp [ys]
    rw [Finset.sum_map_toList]
    calc
      _ ≤ ∑ i∈s, (p i+q i) := Finset.sum_le_sum fun i _ => min_le_right .. 
      _ ≤ ∑' i, (p i+q i) := hs.sum_le_tsum s (fun i _ => hnon i)
      _ ≤ 6 := by linarith
  have concl := SparseHalfLowSmallSide.packed_bound θ hθ hθ' ys hy hyS
  rw [show (ys.map SparseHalfLowSmallSide.g).sum =
      ∑ i ∈ s, SparseHalfLowSmallSide.g (v i) by
    dsimp [ys]
    simp only [List.map_map, Finset.sum_map_toList, Function.comp_apply]] at concl
  exact (Finset.sum_le_sum (fun i _ => rebate i)).trans concl

theorem small_price_bound (p q : ι → ℝ) (θ h : ℝ)
    (hθ : 0≤θ) (hq : ∀ i, 0≤q i) (hqp : ∀ i, q i≤p i)
    (hs : Summable (fun i => p i+q i))
    (hmass : (∑' i, (p i+q i))+h=6) :
    dual p q θ≤θ*(4-h)/2 := by
  have s0 i := (hq i).trans (hqp i)
  have s1 : Summable (fun i => q i) :=
    Summable.of_nonneg_of_le hq (fun i => by linarith [s0 i]) hs
  have H (i : ι) : q i*min θ (p i)≤(θ/2)*(p i+q i) := by
    have L := mul_le_mul_of_nonneg_left (min_le_left θ (p i)) (hq i)
    have U := mul_le_mul_of_nonneg_left (show 2*q i≤p i+q i by linarith [hqp i])
      (show 0≤θ/2 by positivity)
    nlinarith
  have sm := hs.mul_left (θ/2)
  have sf := Summable.of_nonneg_of_le (fun i => mul_nonneg (hq i) (le_min hθ (s0 i))) H sm
  have cmp := Summable.tsum_le_tsum H sf sm
  rw [hs.tsum_mul_left] at cmp
  unfold dual
  nlinarith

/-- A non-strict half-cost obstruction in the zero-heavy chamber
is confined to the two exact endpoint banks. -/
theorem zero_heavy (p q : ι → ℝ) (θ h : ℝ)
    (hθ : 0≤θ ∧ θ≤2)
    (hp : ∀ i, p i≤2) (hq : ∀ i, 0≤q i ∧ q i≤1)
    (hqp : ∀ i, q i≤p i)
    (hs : Summable (fun i => p i+q i))
    (hh : 0≤h) (hmass : (∑' i, (p i+q i))+h=6)
    (obs : 2≤dual p q θ) :
    h=0 ∧ ∃ s : Finset ι,
      ((θ=1 ∧ s.card=3 ∧ (∀ i∈s, p i=1 ∧ q i=1)) ∨
       (θ=2 ∧ s.card=2 ∧ (∀ i∈s, p i=2 ∧ q i=1))) ∧
      (∀ i∉s, p i=0 ∧ q i=0) := by
  have pn i : 0≤p i := (hq i).1.trans (hqp i)
  have h1 : 1≤θ := by
    have hb := small_price_bound p q θ h hθ.1 (fun i => (hq i).1) hqp hs hmass
    nlinarith [mul_nonneg hθ.1 hh]
  have he := interior_bound p q θ h h1 hθ.2 pn hq hs hh hmass
  have ends : θ=1 ∨ θ=2 := by
    by_contra! n
    have m := mul_pos (sub_pos.mpr (lt_of_le_of_ne h1 n.1.symm)) (sub_pos.mpr (lt_of_le_of_ne hθ.2 n.2))
    nlinarith
  rcases ends with rfl | rfl
  · unfold dual at obs
    obtain ⟨hz,s,cs,ins,out⟩ := priceOne p q h hs hq hqp hh hmass (by linarith)
    exact ⟨hz,s,Or.inl ⟨rfl,cs,ins⟩,out⟩
  · unfold dual at obs
    have qeq : (fun i => q i*min 2 (p i)) = (fun i => p i*q i) :=
      funext fun i => by rw [min_eq_right (hp i),mul_comm]
    rw [qeq] at obs
    obtain ⟨hz,s,cs,ins,out⟩ :=
      priceTwo p q h hs (fun i => ⟨pn i,hp i⟩) hq hh hmass (by linarith)
    exact ⟨hz,s,Or.inr ⟨rfl,cs,ins⟩,out⟩

#print axioms interior_bound
#print axioms zero_heavy
end SparseHalfCountableEndpoint
