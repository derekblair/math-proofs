import SeparatorLogic

namespace PackingSeparator

/-- Strict reachability in the graph of a prescribed packing's comparison
edges. The formalization of a particular family supplies its actual edges. -/
def ReachInc {V : Type} (Edges : V → V → Prop) (x y : V) : Prop :=
    ¬Relation.ReflTransGen Edges x y ∧ ¬Relation.ReflTransGen Edges y x

def ReachSeparator {V : Type} (Edges : V → V → Prop) (z : V) : Prop :=
  (∀ x, Relation.ReflTransGen Edges x z ∨ Relation.ReflTransGen Edges z x) ∧
    (∃ x y, Relation.TransGen Edges x z ∧ Relation.TransGen Edges y z ∧ ReachInc Edges x y) ∧
    (∃ x y, Relation.TransGen Edges z x ∧ Relation.TransGen Edges z y ∧ ReachInc Edges x y)

lemma edge_to_path {V A : Type} [Preorder A] {E : V → V → Prop}
    (f : V → A) (h : ∀ x y, E x y → f x ≤ f y)
    {x y : V} (P : Relation.ReflTransGen E x y) : f x ≤ f y := by
  induction P with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (h _ _ e)

lemma reflect_inc {V A : Type} [PartialOrder A] {E : V → V → Prop}
    (f : V → A) (h : ∀ x y, E x y → f x ≤ f y)
    {x y : V} (H : Inc (f x) (f y)) : ReachInc E x y :=
  ⟨fun p => H.1 (edge_to_path f h p),fun p => H.2 (edge_to_path f h p)⟩

lemma certificate_separator {V A : Type} [PartialOrder A] {E : V → V → Prop}
    (f : V → A) (h : ∀ x y, E x y → f x ≤ f y)
    {z a b c d : V}
    (all : ∀ x, Relation.ReflTransGen E x z ∨ Relation.ReflTransGen E z x)
    (al : Relation.TransGen E a z) (bl : Relation.TransGen E b z)
    (cu : Relation.TransGen E z c) (du : Relation.TransGen E z d)
    (left : Inc (f a) (f b)) (right : Inc (f c) (f d)) :
    ReachSeparator E z :=
  ⟨all,⟨a,b,al,bl,reflect_inc f h left⟩,⟨c,d,cu,du,reflect_inc f h right⟩⟩

end PackingSeparator
