import RamseyExactNine

namespace Erdos151Ramsey

variable {V : Type*} [DecidableEq V] (G : V → V → Prop)

def AlphaCap (S : Finset V) (k : Nat) : Prop :=
  ∀ T ⊆ S, Independent G T → T.card ≤ k

def IsolatedIn (L S : Finset V) : Prop :=
  L ⊆ S ∧ ∀ a ∈ L, ∀ b ∈ S, ¬ G a b

theorem isolated_union (sym : ∀ {a b}, G a b → G b a)
    {L S T : Finset V} (hL : IsolatedIn G L S) (hT : T ⊆ S \ L)
    (hi : Independent G T) :
    L ∪ T ⊆ S ∧ Independent G (L ∪ T) ∧ (L ∪ T).card = L.card + T.card := by
  have ht : T ⊆ S := fun x hx => (Finset.mem_sdiff.mp (hT hx)).1
  refine ⟨Finset.union_subset hL.1 ht, ?_, Finset.card_union_of_disjoint ?_⟩
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hL.2 a ha b ((Finset.union_subset hL.1 ht) hb) hab
    · rcases Finset.mem_union.mp hb with hb | hb
      · exact hL.2 b hb a (ht ha) (sym hab)
      · exact hi a ha b hb hab
  · exact Finset.disjoint_left.mpr (fun a haL haT => (Finset.mem_sdiff.mp (hT haT)).2 haL)

theorem add_of_isolated_le (sym : ∀ {a b}, G a b → G b a)
    {L S T : Finset V} {k : Nat} (hL : IsolatedIn G L S) (hT : T ⊆ S \ L)
    (hi : Independent G T) (hc : AlphaCap G S k) :
    L.card + T.card ≤ k := by
  obtain ⟨hs, hind, hcard⟩ := isolated_union G sym hL hT hi
  rw [← hcard]
  exact hc _ hs hind

variable [Fintype V] [DecidableRel G]

theorem private_d10 (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFree G) {S L : Finset V}
    (hL : IsolatedIn G L S) (hc : AlphaCap G S 1) :
    S.card + L.card ≤ 2 := by
  have hS : S.card ≤ 2 := by
    by_contra! hn
    obtain ⟨T, ht, tcard, hi⟩ := independent_two_of_three G sym irr tf S (by omega)
    have := hc T ht hi
    omega
  by_cases hP : (S \ L).Nonempty
  · obtain ⟨x, hx⟩ := hP
    have hT : {x} ⊆ S \ L := Finset.singleton_subset_iff.mpr hx
    have hi : Independent G {x} := by
      intro a ha b hb
      simp only [Finset.mem_singleton] at ha hb
      simpa [ha, hb] using irr x
    have hz := add_of_isolated_le G sym hL hT hi hc
    simp only [Finset.card_singleton] at hz
    omega
  · have he : S \ L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    have hz := add_of_isolated_le G sym hL (Finset.empty_subset (S \ L))
      (by intro a ha; simp at ha) hc
    have ht := Finset.card_sdiff_add_card_eq_card hL.1
    simp [he] at ht
    simp at hz
    omega

theorem private_d9 (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFree G) {S L : Finset V}
    (hL : IsolatedIn G L S) (hc : AlphaCap G S 2) :
    2*S.card + 3*L.card ≤ 10 := by
  have hS : S.card ≤ 5 := by
    by_contra! hn
    obtain ⟨T, ht, tcard, hi⟩ := independent_three_of_six G sym irr tf S (by omega)
    have := hc T ht hi
    omega
  have hz := add_of_isolated_le G sym hL (Finset.empty_subset (S \ L))
    (by intro a ha; simp at ha) hc
  simp at hz
  have hcard := Finset.card_sdiff_add_card_eq_card hL.1
  by_cases he : L.card = 0
  · omega
  by_cases h1 : L.card = 1
  · have h2 : (S \ L).card ≤ 2 := by
      by_contra! hn
      obtain ⟨T, ht, tcard, hi⟩ := independent_two_of_three G sym irr tf (S \ L) (by omega)
      have := add_of_isolated_le G sym hL ht hi hc
      omega
    omega
  · have he' : S \ L = ∅ := by
      by_contra hn
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      have hT : {x} ⊆ S \ L := Finset.singleton_subset_iff.mpr hx
      have hi : Independent G {x} := by
        intro a ha b hb
        simp only [Finset.mem_singleton] at ha hb
        simpa [ha, hb] using irr x
      have := add_of_isolated_le G sym hL hT hi hc
      simp only [Finset.card_singleton] at this
      omega
    simp [he'] at hcard
    omega

theorem private_d8 (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFree G) {S : Finset V} (hc : AlphaCap G S 3) : S.card ≤ 9 := by
  by_contra! hn
  obtain ⟨T, ht, tcard, hi⟩ := independent_four_of_ten G sym irr tf S (by omega)
  have := hc T ht hi
  omega

theorem private_d8_exact (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFree G) {S : Finset V} (hc : AlphaCap G S 3) : S.card ≤ 8 := by
  by_contra! hn
  obtain ⟨T, ht, tcard, hi⟩ := independent_four_of_nine G sym irr tf S (by omega)
  have := hc T ht hi
  omega

def Clique (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G a b

/-- An induced pool having neither an independent triple nor a four-clique has at most
eight vertices. This uses triangle-freeness of the complement of the *pool*, not of G. -/
theorem pool_cap_no_independent3_no_clique4 (sym : ∀ {a b}, G a b → G b a)
    (irr : ∀ a, ¬ G a a) {S : Finset V} (hc : AlphaCap G S 2)
    (hk : ∀ T ⊆ S, Clique G T → T.card ≤ 3) :
    S.card ≤ 8 := by
  let C (a b : V) : Prop := a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ¬ G a b
  letI : DecidableRel C := fun a b => inferInstanceAs
    (Decidable (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ¬ G a b))
  have sy : ∀ {a b}, C a b → C b a := fun h =>
    ⟨h.2.1, h.1, Ne.symm h.2.2.1, fun h' => h.2.2.2 (sym h')⟩
  have ir : ∀ a, ¬ C a a := fun a e => e.2.2.1 rfl
  have tf : TriangleFree C := by
    intro a b c hab hbc hac
    have sub : ({a,b,c} : Finset V) ⊆ S := by
      exact Finset.insert_subset_iff.mpr ⟨hab.1, Finset.insert_subset_iff.mpr
        ⟨hab.2.1, Finset.singleton_subset_iff.mpr hbc.2.1⟩⟩
    have ci : ({a,b,c} : Finset V).card = 3 := by
      have hb : b ∉ ({c} : Finset V) := by simpa only [Finset.mem_singleton] using hbc.2.2.1
      have ha : a ∉ ({b,c} : Finset V) := by
        simp [hab.2.2.1, hac.2.2.1]
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb, Finset.card_singleton]
    have ind : Independent G {a,b,c} := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact irr _
      · exact hab.2.2.2
      · exact hac.2.2.2
      · exact (sy hab).2.2.2
      · exact irr _
      · exact hbc.2.2.2
      · exact (sy hac).2.2.2
      · exact (sy hbc).2.2.2
      · exact irr _
    have contra := hc _ sub ind
    omega
  by_contra! hn
  obtain ⟨T, ht, tcard, hi⟩ := independent_four_of_nine C sy ir tf S (by omega)
  have H : Clique G T := by
    intro a ha b hb ne
    by_contra h
    exact hi a ha b hb ⟨ht ha, ht hb, ne, h⟩
  have := hk T ht H
  omega

#print axioms private_d10
#print axioms private_d9
#print axioms private_d8
#print axioms private_d8_exact
#print axioms pool_cap_no_independent3_no_clique4
end Erdos151Ramsey
