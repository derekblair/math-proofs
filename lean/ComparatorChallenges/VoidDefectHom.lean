import Mathlib

/-! # Void-frame defect homomorphism rigidity and literal-product obstruction (SS-007) -/

open Finset

namespace VoidMonoidParam

variable {α : Type} [Fintype α] [DecidableEq α]

@[ext]
structure Nprime (α : Type) [Fintype α] [DecidableEq α] where
  A : Finset α
  B : Finset α
  hB : B ⊆ A

namespace Nprime

instance : Mul (Nprime α) where
  mul x y := ⟨x.A ∪ y.A, x.B ∪ y.B, Finset.union_subset_union x.hB y.hB⟩

instance : One (Nprime α) where
  one := ⟨∅, ∅, Finset.empty_subset _⟩

end Nprime

end VoidMonoidParam

namespace VoidDefectHom

open VoidMonoidParam

variable {α : Type} [Fintype α] [DecidableEq α]
variable {β : Type} [Fintype β] [DecidableEq β]

def ProdDefectAdditive (F : Finset (Nprime α × Nprime β)) : Prop :=
  ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ →
    Disjoint z₁.1.A z₂.1.A ∧ Disjoint z₁.2.A z₂.2.A

theorem defect_hom_rigidity {M : Type*} [AddCancelCommMonoid M]
    (f : Nprime α → M) (hadd : ∀ x y, f (x * y) = f x + f y) (x : Nprime α) :
    f x = 0 := by
  sorry

theorem literal_product_never
    (F : Finset (Nprime α × Nprime β))
    (a : Nprime α) (hane : a ≠ 1)
    (c : Nprime β) (hcne : c ≠ 1)
    (hz1 : (a, 1) ∈ F) (hz2 : (a, c) ∈ F) :
    ¬ ProdDefectAdditive F := by
  sorry

end VoidDefectHom
