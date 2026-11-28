import RamseySmall
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos151Ramsey
open scoped BigOperators

variable {V : Type*} [DecidableEq V] (G : V → V → Prop) [DecidableRel G]

theorem even_degree_sum (S : Finset V) (sym : ∀ {a b}, G a b → G b a)
    (irr : ∀ a, ¬ G a a) :
    ∃ m : ℕ, ∑ v ∈ S, (S.filter (G v)).card = 2*m := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨m, hm⟩ := ih
    have he (v : V) : ((insert a S).filter (G v)).card =
          (S.filter (G v)).card + if G v a then 1 else 0 := by
      rw [Finset.filter_insert]
      split
      · rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
      · simp
    have hswap (v : V) : (if G v a then (1 : ℕ) else 0) = if G a v then 1 else 0 := by
      have hh : G v a ↔ G a v := ⟨sym, sym⟩
      simp only [hh]
    have hterm : (∑ v ∈ S, if G v a then (1 : ℕ) else 0) = (S.filter (G a)).card := by
      simp_rw [hswap]
      rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
    refine ⟨m+(S.filter (G a)).card, ?_⟩
    rw [Finset.sum_insert ha]
    simp_rw [he, Finset.sum_add_distrib]
    simp [irr, hm, hterm]
    omega


theorem independent_four_of_nine [Fintype V]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (h : TriangleFree G)
    (S : Finset V) (hc : 9 ≤ S.card) :
    ∃ T ⊆ S, 4 ≤ T.card ∧ Independent G T := by
  by_cases hlarge : 10 ≤ S.card
  · exact independent_four_of_ten G sym irr h S hlarge
  have hcard : S.card = 9 := by omega
  by_contra! hn
  have hu (v : V) : (S.filter (G v)).card ≤ 3 := by
    by_contra! hc
    exact hn (S.filter (G v)) (Finset.filter_subset _ _) (by omega) (independent_near G h v S)
  have hl (v : V) (hv : v ∈ S) : 3 ≤ (S.filter (G v)).card := by
    by_contra! hd
    have hf := far_card G irr v S hv
    obtain ⟨T, hT, hc, hi⟩ :=
      independent_three_of_six G sym irr h (far G v S) (by omega)
    have hfar (x : V) (hx : x ∈ T) := Finset.mem_filter.mp (hT hx)
    have hnot : v ∉ T := fun hm => (Finset.mem_erase.mp (hfar v hm).1).1 rfl
    apply hn (insert v T)
    · exact Finset.insert_subset_iff.mpr ⟨hv, fun x hx => Finset.mem_of_mem_erase (hfar x hx).1⟩
    · rw [Finset.card_insert_of_notMem hnot]; omega
    · exact independent_insert G sym irr hi (fun x hx => (hfar x hx).2)
  have hd (v : V) (hv : v ∈ S) : (S.filter (G v)).card = 3 :=
    le_antisymm (hu v) (hl v hv)
  obtain ⟨m, hm⟩ := even_degree_sum G S sym irr
  have hs : (∑ v ∈ S, (S.filter (G v)).card) = ∑ _v ∈ S, (3 : Nat) :=
    Finset.sum_congr rfl hd
  rw [hs] at hm
  simp [hcard] at hm
  omega

theorem ramsey34 (G : Fin 9 → Fin 9 → Prop) [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (h : TriangleFree G) :
    ∃ T, 4 ≤ T.card ∧ Independent G T := by
  obtain ⟨T, _, hc, hi⟩ := independent_four_of_nine G sym irr h Finset.univ (by simp)
  exact ⟨T, hc, hi⟩

#print axioms independent_four_of_nine
#print axioms ramsey34
end Erdos151Ramsey
