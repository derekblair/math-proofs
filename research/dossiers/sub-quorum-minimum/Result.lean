import Lower
import Mathlib.Data.Nat.Log

namespace QuorumMinimum
open Classical QuorumBounds
noncomputable section

theorem clique_achievable_compl {V : Type} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (h : CliqueOn G s) : Achievable Gᶜ s.card := by
  let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe s)
  let f (x : V) : Option (Fin s.card) := if hx : x ∈ s then some (e ⟨x,hx⟩) else none
  refine ⟨f,fun i => ⟨(e.symm i).val,?_⟩,?_⟩
  · have hmem : (e.symm i).val ∈ s := (e.symm i).property
    simp only [f,dite_eq_left hmem,Subtype.coe_eta,Equiv.apply_symm_apply]
  · intro x i hi
    have hx : x ∈ s := by
      by_contra hh
      simp [f,hh] at hi
    have ez : others Gᶜ f x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      simp only [others,Finset.mem_filter,Finset.mem_univ,true_and] at hy
      obtain ⟨adj,j,hj,_⟩ := hy
      have hs : y ∈ s := by
        by_contra hh
        simp [f,hh] at hj
      exact ((SimpleGraph.compl_adj G x y).mp adj).2 (h x hx y hs adj.ne)
    simp [ez]

theorem forbidden_large_clique {V : Type} [Fintype V] (G : SimpleGraph V) :
    NoClique G (psi Gᶜ+1) Finset.univ := by
  intro s _ hs hc
  have h := achievable_le_psi (clique_achievable_compl G s hc)
  omega

theorem psi_order_lower (n : Nat) (G : SimpleGraph (Fin n)) : n < 2^(psi G+psi Gᶜ) := by
  have a := forbidden_large_clique G
  have b : NoClique Gᶜ (psi G+1) Finset.univ := by
    simpa only [compl_compl] using forbidden_large_clique Gᶜ
  simpa [Nat.add_comm] using ramsey_power G Finset.univ _ _ a b

def minSum (n : Nat) : Nat :=
  sInf {m : Nat | ∃ G : SimpleGraph (Fin n), m = psi G + psi Gᶜ}

theorem minSum_order (n : Nat) (hn : 2≤n) :
    Nat.log 2 n + 1 ≤ minSum n ∧ minSum n ≤ 80 * Nat.clog 2 n := by
  let Z := {m : Nat | ∃ G : SimpleGraph (Fin n), m = psi G + psi Gᶜ}
  let E : SimpleGraph (Fin n) := ⊥
  have nz : Z.Nonempty := ⟨psi E+psi Eᶜ,E,rfl⟩
  obtain ⟨F,hF⟩ : ∃ G : SimpleGraph (Fin n), minSum n = psi G + psi Gᶜ :=
    Nat.sInf_mem nz
  obtain ⟨G,hG⟩ := psi_order_upper n (Nat.clog 2 n)
    (Nat.clog_pos (by decide) (by omega)) (Nat.le_pow_clog (by decide) n)
  have lo : n < 2^(minSum n) := hF ▸ psi_order_lower n F
  exact ⟨(Nat.log_lt_iff_lt_pow (by decide : 1 < (2 : Nat)) (by omega : n ≠ 0)).mpr lo,
    (Nat.sInf_le (show psi G + psi Gᶜ ∈ Z from ⟨G,rfl⟩)).trans hG⟩

#print axioms psi_order_lower
#print axioms minSum_order
end
end QuorumMinimum
