import CountableDual
import OneHeavyPacking
import TwoHeavyDual

namespace SparseHalfCountableEndpoint
open SparseHalfLowSmallSide
variable {ι : Type*}

/-- Any finite-subfamily light rebate inequality persists on a summable bank. -/
theorem light_rebate (p q : ι → ℝ) (θ : ℝ) (t : ℝ) (hθ : 0≤θ)
    (hp : ∀ i, 0≤p i) (hq : ∀ i, 0≤q i ∧ q i≤1)
    (hs : Summable (fun i => p i+q i)) (hS : (∑' i,(p i+q i))≤t) :
    (∑' i, q i*min θ (p i))≤g t := by
  have s0 i : 0≤p i+q i := add_nonneg (hp i) (hq i).1
  have sumQ : Summable (fun i => q i * min θ (p i)) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro i; exact mul_nonneg (hq i).1 (le_min hθ (hp i))
    · intro i
      exact (mul_le_mul (hq i).2 (min_le_right θ (p i))
        (le_min hθ (hp i)) (by norm_num)).trans (by linarith [(hq i).1])
  apply sumQ.tsum_le_of_sum_le
  intro s
  let bs := s.toList.map fun i => (p i,q i)
  have f : ∀ b ∈ bs, 0≤b.1 ∧ 0≤b.2 ∧ b.2≤1 := by
    intro b hb
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    exact ⟨hp i,(hq i).1,(hq i).2⟩
  have h := SparseHalfTwoHeavyDual.light_sum bs θ f
  simp only [bs, List.map_map, Finset.sum_map_toList, Function.comp_apply] at h
  exact h.trans (monotone_nonneg (Finset.sum_nonneg fun i _ => s0 i)
    ((hs.sum_le_tsum s (fun i _ => s0 i)).trans hS))

/-- Sharp packed light contribution, now uniformly valid for infinitely
many light blocks. This is the normalized one-heavy endpoint envelope. -/
theorem one_heavy_rebate (p q : ι → ℝ) (θ u : ℝ)
    (hθ : 1≤θ) (hu : 2≤u) (hu' : u≤4)
    (hp : ∀ i, 0≤p i) (hq : ∀ i, 0≤q i ∧ q i≤1)
    (hs : Summable (fun i => p i+q i)) (hS : (∑' i,(p i+q i))≤8-2*u) :
    (∑' i, q i*min θ (p i))≤ SparseHalfOneHeavyNormalized.base θ u := by
  have s0 i : 0≤p i+q i := add_nonneg (hp i) (hq i).1
  have sumQ : Summable (fun i => q i * min θ (p i)) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro i; exact mul_nonneg (hq i).1 (le_min (by linarith) (hp i))
    · intro i
      exact (mul_le_mul (hq i).2 (min_le_right θ (p i))
        (le_min (by linarith) (hp i)) (by norm_num)).trans (by linarith [(hq i).1])
  apply sumQ.tsum_le_of_sum_le
  intro s
  let v := fun i => min (θ+1) (p i+q i)
  let ys := s.toList.map v
  have hy : ∀ x∈ys, 0≤x ∧ x≤θ+1 := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨le_min (by linarith) (s0 i),min_le_left ..⟩
  have hyS : ys.sum≤8-2*u := by
    dsimp [ys]
    rw [Finset.sum_map_toList]
    exact (Finset.sum_le_sum (fun i _ => min_le_right (θ+1) (p i+q i))).trans
      ((hs.sum_le_tsum s (fun i _ => s0 i)).trans hS)
  have h := SparseHalfOneHeavyPacking.packed_le θ (8-2*u) hθ (by linarith) (by linarith) ys hy hyS
  have eq : 8-2*u-(θ+1)=7-2*u-θ := by ring
  rw [eq,←SparseHalfOneHeavyNormalized.base] at h
  simp only [ys,List.map_map, Finset.sum_map_toList, Function.comp_apply] at h
  exact (Finset.sum_le_sum (fun i _ => block_rebate θ (p i) (q i) hθ (hq i).1 (hq i).2)).trans h

#print axioms light_rebate
#print axioms one_heavy_rebate
end SparseHalfCountableEndpoint
