import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# The r47 saturated nine-element Sidon witness

The predicates below express uniqueness of unordered pair sums (including
diagonal pairs) and maximality inside the finite interval. The concrete checks
are evaluated by Lean's kernel, not by `native_decide` or external certificates.
Search exhaustiveness, minimality, and historical priority are not asserted.
-/

namespace SidonSat184

/-- Every equality of pair sums comes from the same unordered pair. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon subset of `[1,N]` to which no further interval element can be added. -/
def IsSaturated (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Finset.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

def astar : Finset ℕ := {16, 62, 66, 74, 88, 104, 117, 122, 123}

theorem sidon_subset {A B : Finset ℕ} (hAB : A ⊆ B) (hB : IsSidon B) : IsSidon A := by
  intro a ha b hb c hc d hd hab
  exact hB a (hAB ha) b (hAB hb) c (hAB hc) d (hAB hd) hab

/-- If `insert x A` is Sidon and every addable point outside `A` equals `x`,
then `insert x A` saturates the interval. -/
theorem unique_extension_saturated {A : Finset ℕ} {N x : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hx : x ∈ Finset.Icc 1 N)
    (hs : IsSidon (insert x A))
    (hunique : ∀ y ∈ Finset.Icc 1 N, y ∉ A → IsSidon (insert y A) → y = x) :
    IsSaturated (insert x A) N := by
  refine ⟨Finset.insert_subset hx hA, hs, ?_⟩
  intro y hy hyn hys
  have hyA : y ∉ A := fun h => hyn (Finset.mem_insert_of_mem h)
  have hsmall : IsSidon (insert y A) := sidon_subset
    (Finset.insert_subset_insert y (Finset.subset_insert x A)) hys
  have he := hunique y hy hyA hsmall
  exact hyn (he ▸ Finset.mem_insert_self x A)

theorem astar_card : astar.card = 9 := by decide

theorem astar_in_interval : astar ⊆ Finset.Icc 1 184 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem astar_sidon : IsSidon astar := by
  unfold IsSidon astar
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem astar_no_extension :
    ∀ x ∈ Finset.Icc 1 184, x ∉ astar → ¬ IsSidon (insert x astar) := by
  unfold IsSidon astar
  decide

/-- The complete finite witness claim, including size, containment, and maximality. -/
theorem r47_sat184 : astar.card = 9 ∧ IsSaturated astar 184 :=
  ⟨astar_card, astar_in_interval, astar_sidon, astar_no_extension⟩

end SidonSat184
