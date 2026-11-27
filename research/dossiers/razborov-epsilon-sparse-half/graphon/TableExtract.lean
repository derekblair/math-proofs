import TableConsistency
import Mathlib.Order.Filter.Finite

open Filter Set Topology Function
open scoped BigOperators
namespace SparseHalfGraphon

/-- Extract cell and rectangle integrals and stabilize each finite parent map
at once, for uniformly padded finite labels. -/
theorem coherent_table_subsequence (d : ℕ → ℕ)
    (P : ℕ → ∀ n, Fin (d (n+1)) → Fin (d n))
    (A : ∀ k, CoherentTables (fun n => Fin (d n)) (P k)) :
    ∃ q : ℕ → ℕ, ∃ p : ∀ n, Fin (d (n+1)) → Fin (d n),
    ∃ B : CoherentTables (fun n => Fin (d n)) p,
      StrictMono q ∧ (∀ n, ∀ᶠ k in atTop, P (q k) n = p n) ∧
      (∀ n i, Tendsto (fun k => (A (q k)).cell n i) atTop (𝓝 (B.cell n i))) ∧
      (∀ n i j, Tendsto (fun k => (A (q k)).joint n i j) atTop (𝓝 (B.joint n i j))) := by
  classical
  let Parent := (n : ℕ) × Fin (d (n+1))
  let Readings := (n : ℕ) × (Fin (d n) ⊕ (Fin (d n) × Fin (d n)))
  let parent : ℕ → (i : Parent) → Fin (d i.1) := fun k i => P k i.1 i.2
  obtain ⟨r, p₀, hr, hp₀⟩ := table_diagonal parent
  let p : ∀ n, Fin (d (n+1)) → Fin (d n) := fun n i => p₀ ⟨n,i⟩
  have hparent : ∀ n, ∀ᶠ k in atTop, P (r k) n = p n := by
    intro n
    have hh : ∀ᶠ k in atTop, ∀ i, P (r k) n i = p n i := by
      apply eventually_all.mpr
      intro i
      have hh := hp₀ ⟨n,i⟩
      rw [nhds_discrete, tendsto_pure] at hh
      exact hh
    exact hh.mono (fun _ h => funext h)
  have hCell (k n) (i : Fin (d n)) : (A k).cell n i ≤ 1 := by
    rw [← (A k).cell_total n]
    exact Finset.single_le_sum (fun j _ => (A k).cell_zero n j) (Finset.mem_univ i)
  let readings : ℕ → Readings → ℝ := fun k i => match i with
    | ⟨n, .inl j⟩ => (A (r k)).cell n j
    | ⟨n, .inr (i,j)⟩ => (A (r k)).joint n i j
  have h₀ (k) (i : Readings) : 0 ≤ readings k i := by
    rcases i with ⟨n,i|⟨i,j⟩⟩
    · exact (A (r k)).cell_zero n i
    · exact (A (r k)).joint_zero n i j
  have h₁ (k) (i : Readings) : readings k i ≤ 1 := by
    rcases i with ⟨n,i|⟨i,j⟩⟩
    · exact hCell (r k) n i
    · apply ((A (r k)).joint_bound n i j).trans
      calc
        _ ≤ 1 * (A (r k)).cell n j :=
          mul_le_mul_of_nonneg_right (hCell (r k) n i) ((A (r k)).cell_zero n j)
        _ ≤ 1 := by simpa only [one_mul] using hCell (r k) n j
  obtain ⟨s, b, hs, _, hb⟩ := interval_table_diagonal readings h₀ h₁
  let q := r ∘ s
  have hq : ∀ n, ∀ᶠ k in atTop, P (q k) n = p n :=
    fun n => hs.tendsto_atTop.eventually (hparent n)
  let B := limit_coherent_tables (fun k => A (q k)) hq
    (fun n i => b ⟨n, .inl i⟩) (fun n i j => b ⟨n, .inr (i,j)⟩)
    (fun n i => hb ⟨n, .inl i⟩) (fun n i j => hb ⟨n, .inr (i,j)⟩)
  exact ⟨q,p,B,hr.comp hs,hq,(fun n i => hb ⟨n,.inl i⟩),(fun n i j => hb ⟨n,.inr (i,j)⟩)⟩

#print axioms coherent_table_subsequence
end SparseHalfGraphon
