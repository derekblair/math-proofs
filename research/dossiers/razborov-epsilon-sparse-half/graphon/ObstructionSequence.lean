import FiniteBlowup
import GreedyEndpointExclusion
import FiniteSaturatedSequence
import PaddedTowerScale

open Set MeasureTheory Function Filter Topology
open scoped BigOperators
namespace SparseHalfGraphon

structure Obstruction (n : ℕ) where
  pos : 0 < n
  adj : Fin n → Fin n → Bool
  sym : ∀ u v, adj u v=adj v u
  loop : ∀ u, adj u u=false
  tf : ∀ u v w, adj u v=true  →  adj u w=true  →  adj v w=false
  mark : Finset (Fin n)
  mark_ind : IndependentCells adj (mark:Set (Fin n))
  mark_max : ∀ s : Finset (Fin n), IndependentCells adj (s:Set (Fin n))  → 
    s.card ≤ mark.card
  bad : 1/50 < beta uniformVertices (adjacencyKernel adj sym)

noncomputable def Obstruction.alpha {n : ℕ} (Q : Obstruction n) : ℝ := (Q.mark.card:ℝ)/n

theorem Obstruction.alpha_cap {n : ℕ} (Q : Obstruction n)
    (s : Finset (Fin n)) (h : IndependentCells Q.adj (s:Set (Fin n))) :
    (s.card:ℝ)/(Fintype.card (Fin n):ℝ) ≤ Q.alpha := by
  unfold Obstruction.alpha
  simp only [Fintype.card_fin]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Q.mark_max s h) (Nat.cast_nonneg _)

def obstructionVertices (n : ℕ → ℕ) (k:ℕ) :=
  Fin (n k) × Fin (2*(k+1))

instance (n : ℕ → ℕ) (k : ℕ) : Fintype (obstructionVertices n k) :=
  inferInstanceAs (Fintype (Fin (n k) × Fin (2*(k+1))))
instance (n : ℕ → ℕ) (k : ℕ) : MeasurableSpace (obstructionVertices n k) :=
  inferInstanceAs (MeasurableSpace (Fin (n k) × Fin (2*(k+1))))
instance (n : ℕ → ℕ) (k : ℕ) : MeasurableSingletonClass (obstructionVertices n k) :=
  inferInstanceAs (MeasurableSingletonClass (Fin (n k) × Fin (2*(k+1))))
instance (n : ℕ → ℕ) (k : ℕ) : DecidableEq (obstructionVertices n k) :=
  inferInstanceAs (DecidableEq (Fin (n k) × Fin (2*(k+1))))

/-- A canonical sequence with growing even orders is obtained by taking
independent clone blow-ups. Neither beta nor the normalized alpha changes. -/
theorem obstruction_sequence
    (fail : ∀ ε > 0, ∃ n : ℕ, ∃ Q : Obstruction n, 2/5-ε ≤ Q.alpha) :
    ∃ n : ℕ → ℕ, ∃ G : ∀ k,obstructionVertices n k → obstructionVertices n k → Bool,
    ∃ sym : ∀ k u v,G k u v=G k v u,
    ∃ A : ∀ k,Finset (obstructionVertices n k), ∃ a : ℕ → ℝ,
      (∀ k u, G k u u=false) ∧
      (∀ k u v w,G k u v=true  →  G k u w=true  →  G k v w=false) ∧
      (∀ k,Fintype.card (obstructionVertices n k)=2*(n k*(k+1))) ∧
      (∀ k,0 < Fintype.card (obstructionVertices n k)) ∧
      Tendsto (fun k=>Fintype.card (obstructionVertices n k)) atTop atTop ∧
      (∀ k, IndependentCells (G k) (A k:Set (obstructionVertices n k))) ∧
      (∀ k, a k=((A k).card:ℝ)/(Fintype.card (obstructionVertices n k):ℝ)) ∧
      (∀ k,39/100 ≤ a k) ∧ Tendsto a atTop (𝓝 (2/5)) ∧
      (∀ k (s : Finset (obstructionVertices n k)), IndependentCells (G k) (s:Set (obstructionVertices n k))  → 
        (s.card:ℝ)/(Fintype.card (obstructionVertices n k):ℝ) ≤ a k) ∧
      (∀ k,1/50 < beta uniformVertices (adjacencyKernel (G k) (sym k))) := by
  let ε (k : ℕ) := canonicalScale k/100
  have εp (k : ℕ) : 0 < ε k := div_pos (canonicalScale_pos k) (by norm_num)
  have H (k) := fail (ε k) (εp k)
  choose n Q hp using H
  let V := obstructionVertices n
  let G (k) : V k → V k → Bool := blownAdj (Q k).adj
  let sym (k) : ∀ u v,G k u v=G k v u := blown_sym (Q k).adj (Q k).sym
  let A (k) : Finset (V k) := (Q k).mark.product (Finset.univ : Finset (Fin (2*(k+1))))
  let a (k) : ℝ := (Q k).alpha
  have posU (k) : 0 < Fintype.card (Fin (2*(k+1))) := by simp
  have posV (k) : 0 < Fintype.card (V k) := by
    change 0 < Fintype.card (Fin (n k) × Fin (2*(k+1)))
    simpa [Fintype.card_prod] using Nat.mul_pos (Q k).pos (show 0 < 2*(k+1) from by omega)
  have hN k : Fintype.card (V k)=2*(n k*(k+1)) := by
    change Fintype.card (Fin (n k) × Fin (2*(k+1)))=_
    simp only [Fintype.card_prod,Fintype.card_fin]
    ring
  have hLoop k : ∀ u,G k u u=false := blown_loop (Q k).adj (Q k).loop
  have hTf k : ∀ u v w,G k u v=true  →  G k u w=true  →  G k v w=false :=
    blown_triangle (Q k).adj (Q k).tf
  have hA k : IndependentCells (G k) (A k:Set (V k)) :=
    blown_independent (Q k).adj (Q k).mark (Q k).mark_ind
  have hAm k : a k=((A k).card:ℝ)/(Fintype.card (V k):ℝ) := by
    have hh := blown_mark_mass (Q k).mark (posU k)
    simpa only [a,A,V,obstructionVertices,Obstruction.alpha,Fintype.card_fin] using hh.symm
  have hBeta k : 1/50 < beta uniformVertices (adjacencyKernel (G k) (sym k)) := by
    exact (blown_beta (Q k).adj (Q k).sym (by simpa using (Q k).pos) (posU k)).symm ▸ (Q k).bad
  have hCap k : ∀ s : Finset (V k), IndependentCells (G k) (s:Set (V k))  → 
      (s.card:ℝ)/(Fintype.card (V k):ℝ) ≤ a k :=
    blown_alpha (Q k).adj (by simpa using (Q k).pos) (posU k) (a k) (Q k).alpha_cap
  have hUpper k : a k < 2/5 :=
    finite_bad_alpha_lt_endpoint (G k) (sym k) (hLoop k) (hTf k) _ (hN k) (posV k)
      (A k) (hA k) (a k) (hAm k) (hCap k) (hBeta k)
  have hLower k : 39/100 ≤ a k := by
    have hε : ε k ≤ 1/100 := by
      unfold ε canonicalScale
      have h : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [(show (0:ℝ) ≤ (k:ℝ) by positivity)]
      have hh := inv_le_one_of_one_le₀ h
      linarith
    linarith [hp k]
  have hLim : Tendsto a atTop (𝓝 (2/5)) := by
    have hε : Tendsto ε atTop (𝓝 0) := by simpa using canonicalScale_tendsto.div_const (100:ℝ)
    have hh : Tendsto (fun k=>2/5-ε k) atTop (𝓝 (2/5)) := by
      simpa using (tendsto_const_nhds (x:=(2/5:ℝ))).sub hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hh tendsto_const_nhds hp (fun k=>(hUpper k).le)
  have hgrow : Tendsto (fun k=>Fintype.card (V k)) atTop atTop := by
    apply tendsto_atTop_mono (g:=fun k=>Fintype.card (V k)) (f:=id) (fun k=>?_) tendsto_id
    rw [hN]
    change k ≤ 2*(n k*(k+1))
    have H := Nat.mul_le_mul_right (k+1) (show 1 ≤ n k from (Q k).pos)
    omega
  exact ⟨n,G,sym,A,a,hLoop,hTf,hN,posV,hgrow,hA,hAm,hLower,hLim,hCap,hBeta⟩

#print axioms obstruction_sequence
end SparseHalfGraphon
