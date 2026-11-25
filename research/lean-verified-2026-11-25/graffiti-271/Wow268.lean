import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

open scoped BigOperators

namespace Wow268

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered pairs of distinct center vertices, as in the catalogue. -/
noncomputable def centerPairs (G : SimpleGraph V) : Finset (V × V) :=
  by classical exact Finset.univ.filter fun p => p.1 ∈ G.center ∧ p.2 ∈ G.center ∧ p.1 ≠ p.2

noncomputable def avg (G : SimpleGraph V) : ℚ :=
  (↑(∑ p ∈ centerPairs G, G.dist p.1 p.2) : ℚ) / ↑(centerPairs G).card

def TotalDominating (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, ∃ u ∈ S, G.Adj v u

lemma totalDominating_two_le {G : SimpleGraph V} [Nonempty V] {S : Finset V}
    (h : TotalDominating G S) : 2 ≤ S.card := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨a, ha, _⟩ := h v
  obtain ⟨b, hb, hab⟩ := h a
  have hlt : 1 < S.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab.ne⟩
  omega

lemma avg_lt_of_pointwise_and_strict {I : Type*} (s : Finset I) (f : I → ℕ)
    (k : ℕ) (hk : 0 < k) (hb : ∀ i ∈ s, f i ≤ k)
    (hs : s.Nonempty → ∃ i ∈ s, f i < k) :
    (↑(∑ i ∈ s, f i) : ℚ) / ↑s.card < k := by
  classical
  by_cases he : s.Nonempty
  · obtain ⟨i, hi, hlt⟩ := hs he
    have hsum : (∑ j ∈ s, f j) < ∑ _j ∈ s, k :=
      Finset.sum_lt_sum hb ⟨i, hi, hlt⟩
    have hc : (0 : ℚ) < s.card := by exact_mod_cast he.card_pos
    apply (div_lt_iff₀ hc).2
    simp at hsum
    exact_mod_cast hsum.trans_eq (Nat.mul_comm _ _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simpa using (show (0 : ℚ) < k by exact_mod_cast hk)

lemma member_centerPairs {G : SimpleGraph V} {p : V × V} :
    p ∈ centerPairs G ↔ p.1 ∈ G.center ∧ p.2 ∈ G.center ∧ p.1 ≠ p.2 := by
  classical simp [centerPairs]

lemma center_dist_le {G : SimpleGraph V} {a b : V} {k : ℕ}
    (ha : a ∈ G.center) (hk : G.radius ≤ k) : G.dist a b ≤ k := by
  have h := (SimpleGraph.edist_le_eccent (G := G) (u := a) (v := b))
  rw [G.mem_center_iff a |>.1 ha] at h
  exact ENat.toNat_le_toNat (h.trans hk) (by simp)

lemma conclude {G : SimpleGraph V} {s : ℕ} (hs : 2 ≤ s)
    (hr : G.radius ≤ s)
    (he : G.radius = s → ∃ a ∈ G.center, ∃ b ∈ G.center, G.Adj a b) :
    ⌊1 + avg G⌋ ≤ (s : ℤ) := by
  have hlt : avg G < s := by
    apply avg_lt_of_pointwise_and_strict _ _ _ (by omega)
    · intro p hp
      exact center_dist_le (member_centerPairs.mp hp).1 hr
    · intro hn
      by_cases hEq : G.radius = s
      · obtain ⟨a, ha, b, hb, hab⟩ := he hEq
        refine ⟨(a,b), member_centerPairs.mpr ⟨ha, hb, hab.ne⟩, ?_⟩
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab]
        omega
      · obtain ⟨p,hp⟩ := hn
        have hs0 : 0 < s := by omega
        have hk : G.radius ≤ (↑(s-1) : ℕ∞) := by
          have hl := lt_of_le_of_ne hr hEq
          exact ENat.le_sub_one_of_lt (by exact hl)
        exact ⟨p, hp, (center_dist_le (member_centerPairs.mp hp).1 hk).trans_lt (by omega)⟩
  apply Int.lt_add_one_iff.mp
  rw [Int.floor_lt]
  push_cast
  linarith

end Wow268
