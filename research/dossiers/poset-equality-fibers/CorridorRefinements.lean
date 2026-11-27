import Mathlib.Tactic

namespace CorridorRefinements

theorem principal_fiber_weight_mono {σ W : Type*} [Preorder W] [DecidableLE W]
    (s : Finset σ) (lower : σ → W) :
    Monotone (fun w => (s.filter fun k => lower k ≤ w).card) := by
  classical
  intro u v huv
  apply Finset.card_le_card
  intro k hk
  obtain ⟨h, hku⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨h, hku.trans huv⟩

theorem degree_capacity {α β : Type*} (A₀ A : Finset α) (B₀ B : Finset β)
    (hA : A₀ ⊆ A) (hB : B₀ ⊆ B)
    (r : α → β → Prop) [∀ a b, Decidable (r a b)]
    (hclosed : ∀ a ∈ A₀, ∀ b ∈ B, r a b → b ∈ B₀) :
    (∑ a ∈ A₀, (B.filter fun b => r a b).card) ≤
      ∑ b ∈ B₀, min A₀.card (A.filter fun a => r a b).card := by
  classical
  have he (a) (ha : a ∈ A₀) : (B.filter fun b => r a b) =
      (B₀.filter fun b => r a b) := by
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨h1,h2⟩ => ⟨hclosed a ha b h1 h2,h2⟩,
      fun ⟨h1,h2⟩ => ⟨hB h1,h2⟩⟩
  calc
    (∑ a ∈ A₀, (B.filter fun b => r a b).card) =
        ∑ a ∈ A₀, (B₀.filter fun b => r a b).card :=
      Finset.sum_congr rfl fun a ha => congrArg Finset.card (he a ha)
    _ = ∑ b ∈ B₀, (A₀.filter fun a => r a b).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ b ∈ B₀, min A₀.card (A.filter fun a => r a b).card := by
      apply Finset.sum_le_sum
      intro b hb
      apply le_min (Finset.card_filter_le _ _)
      apply Finset.card_le_card
      exact Finset.filter_subset_filter _ hA

end CorridorRefinements

#print axioms CorridorRefinements.degree_capacity
