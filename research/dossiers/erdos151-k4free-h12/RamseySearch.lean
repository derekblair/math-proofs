import RamseySmall
import Mathlib.Data.Finset.Max

namespace Erdos151Ramsey
variable {n : ℕ}

def findIndependent (adj : Fin n → Fin n → Bool) : ℕ → List (Fin n) → Bool
  | 0, _ => true
  | k+1, xs =>
    if xs.length < k+1 then false else
    xs.any (fun v => findIndependent adj k (xs.filter (fun u => decide (v < u) && !adj v u)))

theorem find_complete (adj : Fin n → Fin n → Bool) (k : ℕ) (xs : List (Fin n))
    (S : Finset (Fin n)) (hS : ∀ v ∈ S, v ∈ xs)
    (hind : Independent (fun u v => adj u v = true) S)
    (hc : k ≤ S.card) : findIndependent adj k xs = true := by
  induction k generalizing xs S with
  | zero => rfl
  | succ k ih =>
    have hp := show S.Nonempty from Finset.card_pos.mp (by omega)
    let v := S.min' hp
    have hv : v ∈ S := Finset.min'_mem S hp
    have len : k+1 ≤ xs.length := by
      have hsub : S ⊆ xs.toFinset := fun x hx => List.mem_toFinset.mpr (hS x hx)
      exact hc.trans ((Finset.card_le_card hsub).trans (List.toFinset_card_le _))
    simp only [findIndependent, if_neg (Nat.not_lt.mpr len), List.any_eq_true]
    refine ⟨v, hS v hv, ih _ (S.erase v) ?_ ?_ ?_⟩
    · intro u hu
      have ⟨hne, huS⟩ := Finset.mem_erase.mp hu
      have hlt : v < u := lt_of_le_of_ne (Finset.min'_le S u huS) hne.symm
      exact List.mem_filter.mpr ⟨hS u huS, by have hno : adj v u ≠ true := hind v hv u huS; simp [hlt, Bool.eq_false_iff.mpr hno]⟩
    · exact fun a ha b hb => hind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    · have := Finset.card_erase_add_one hv
      omega

theorem bound_of_per_vertex (adj : Fin n → Fin n → Bool) (k : ℕ)
    (h : ∀ v, findIndependent adj k ((List.finRange n).filter
      (fun u => decide (v < u) && !adj v u)) = false) :
    ∀ S : Finset (Fin n), Independent (fun u v => adj u v = true) S → S.card ≤ k := by
  intro S hind
  by_contra! hn
  have ht := find_complete adj (k+1) (List.finRange n) S (fun v _ => List.mem_finRange v) hind (by omega)
  have hf : findIndependent adj (k+1) (List.finRange n) = false := by
    simp only [findIndependent, h, List.any_eq_false, forall_const, imp_true_iff]
    split <;> simp
  rw [ht] at hf
  contradiction

#print axioms find_complete
#print axioms bound_of_per_vertex
end Erdos151Ramsey
