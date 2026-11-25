import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic

namespace Wow268

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def side (G : SimpleGraph V) (x z : V) : Finset V :=
  Finset.univ.filter fun y => G.dist z y + 1 = G.dist x y

lemma dist_le_card_side (h : G.Connected) {x z y : V} (hxz : G.Adj x z)
    (hy : y ∈ side G x z) : G.dist x y ≤ (side G x z).card := by
  simp only [side, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨p, hp, hpl⟩ := h.exists_path_of_dist z y
  have hsub : p.support.toFinset ⊆ side G x z := by
    intro q hq
    have hqp : q ∈ p.support := List.mem_toFinset.mp hq
    have h1 := SimpleGraph.length_eq_dist_of_subwalk hpl (p.isSubwalk_takeUntil hqp)
    have h2 := SimpleGraph.length_eq_dist_of_subwalk hpl (p.isSubwalk_dropUntil hqp)
    have happ := congrArg SimpleGraph.Walk.length (p.take_spec hqp)
    rw [SimpleGraph.Walk.length_append, h1, h2, hpl] at happ
    have ha : G.dist x q ≤ G.dist z q + 1 := by
      have ht := h.dist_triangle (u := x) (v := z) (w := q)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxz] at ht
      omega
    have hb := h.dist_triangle (u := x) (v := q) (w := y)
    simp only [side, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support, hpl] at hc
  omega

lemma exists_first_side (h : G.Connected) {x y : V} (hxy : x ≠ y) :
    ∃ z, G.Adj x z ∧ y ∈ side G x z := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist x y
  cases p with
  | nil => exact (hxy rfl).elim
  | @cons x z y hxz q =>
    have h1 := SimpleGraph.dist_le q
    have h2 := h.dist_triangle (u := x) (v := z) (w := y)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxz] at h2
    refine ⟨z, hxz, ?_⟩
    simp only [side, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

lemma balanced_side (h : G.IsTree) {x : V}
    (hx : ∀ z, (∑ y, G.dist x y) ≤ ∑ y, G.dist z y)
    {z : V} (hxz : G.Adj x z) : 2 * (side G x z).card ≤ Fintype.card V := by
  let A := side G x z
  have hg (y : V) : (G.dist x y : ℤ) - (G.dist z y : ℤ) = if y ∈ A then 1 else -1 := by
    have hc := h.dist_eq_dist_add_one_of_adj y hxz
    rw [G.dist_comm (u := y) (v := x), G.dist_comm (u := y) (v := z)] at hc
    simp only [A, side, Finset.mem_filter, Finset.mem_univ, true_and]
    split <;> omega
  have hsum : (∑ y, (G.dist x y : ℤ)) - ∑ y, (G.dist z y : ℤ) =
      2 * (A.card : ℤ) - Fintype.card V := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [hg]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (p := fun y => y ∈ A)
    have hf : Finset.univ.filter (fun y => y ∈ A) = A := by ext y; simp
    rw [hf] at hc
    rw [hf]
    simp at hc
    omega
  have hmin : (∑ y, (G.dist x y : ℤ)) ≤ ∑ y, (G.dist z y : ℤ) := by
    exact_mod_cast hx z
  change 2 * A.card ≤ _
  omega

lemma side_flip (h : G.IsTree) {x z : V} (hxz : G.Adj x z) :
    side G z x = (side G x z)ᶜ := by
  ext y
  have hc := h.dist_eq_dist_add_one_of_adj y hxz
  rw [G.dist_comm (u := y) (v := x), G.dist_comm (u := y) (v := z)] at hc
  simp only [side, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  omega

lemma adjacent_small_ecc_tree [Nontrivial V] (h : G.IsTree) {k : ℕ} (hk : 0 < k)
    (hn : Fintype.card V ≤ 2*k) :
    ∃ x z, G.Adj x z ∧ (∀ y, G.dist x y ≤ k) ∧ (∀ y, G.dist z y ≤ k) := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_min_image (Finset.univ : Finset V)
    (fun x => ∑ y, G.dist x y) Finset.univ_nonempty
  have hb (z : V) (hz : G.Adj x z) : (side G x z).card ≤ k := by
    have hh := balanced_side h (fun z => hx z (Finset.mem_univ _)) hz
    omega
  have hxk (y : V) : G.dist x y ≤ k := by
    by_cases hxy : x = y
    · simp [hxy]
    obtain ⟨z, hz, hy⟩ := exists_first_side h.connected hxy
    exact (dist_le_card_side h.connected hz hy).trans (hb z hz)
  by_cases hex : ∃ z, G.Adj x z ∧ (side G x z).card = k
  · obtain ⟨z, hz, hc⟩ := hex
    refine ⟨x, z, hz, hxk, fun y => ?_⟩
    by_cases hy : y ∈ side G x z
    · have hh := hxk y
      simp only [side, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      omega
    · have hflip : y ∈ side G z x := by simpa [side_flip h hz] using hy
      have hcard : (side G z x).card ≤ k := by
        rw [side_flip h hz, Finset.card_compl, hc]
        omega
      exact (dist_le_card_side h.connected hz.symm hflip).trans hcard
  · have hxsmall (y : V) : G.dist x y < k := by
      by_cases hxy : x = y
      · simpa [hxy] using hk
      obtain ⟨z, hz, hy⟩ := exists_first_side h.connected hxy
      have hle := hb z hz
      have hne : (side G x z).card ≠ k := fun he => hex ⟨z, hz, he⟩
      exact (dist_le_card_side h.connected hz hy).trans_lt (lt_of_le_of_ne hle hne)
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨z, hz, _⟩ := exists_first_side h.connected hy.symm
    refine ⟨x, z, hz, hxk, fun v => ?_⟩
    have ht := h.connected.dist_triangle (u := z) (v := x) (w := v)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hz.symm] at ht
    have ht2 := hxsmall v
    omega

end Wow268
