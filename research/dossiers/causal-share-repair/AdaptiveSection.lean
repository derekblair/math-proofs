import Mathlib.Algebra.Group.Subgroup.Ker

namespace AdaptiveSection

/-- Algebraic step for a causal lift: adding the independent vertical
correction places every required new direction in the extended support. -/
theorem add_section_correction {A B : Type*} [AddGroup A] [AddGroup B]
    (pi : A →+ B) (K : AddSubgroup A) (W : Set B) (sec : B → A)
    (mapIn : ∀ k ∈ K, pi k ∈ W)
    (secK : ∀ k ∈ K, sec (pi k) ∈ K)
    (rightInv : ∀ w ∈ W, pi (sec w) = w)
    (k : A) (hk : k ∈ K) :
    ∃ w ∈ W, ∃ z ∈ K ⊓ pi.ker, z + sec w = k := by
  refine ⟨pi k, mapIn k hk, k - sec (pi k), ?_, sub_add_cancel _ _⟩
  refine ⟨K.sub_mem hk (secK k hk), ?_⟩
  change pi (k - sec (pi k)) = 0
  rw [map_sub, rightInv _ (mapIn k hk), sub_self]

/-- For a fixed previously emitted pad, distinct fresh kernel corrections
produce exactly distinct possible next states, with no change to the past. -/
theorem correction_injective {A B : Type*} [AddGroup A] [AddGroup B]
    (pi : A →+ B) (K : AddSubgroup A) (v : A) :
    Function.Injective (fun z : ↥(K ⊓ pi.ker) => z.1 + v) := by
  intro x y eq
  exact Subtype.ext (add_right_cancel eq)

#print axioms add_section_correction
#print axioms correction_injective
end AdaptiveSection
