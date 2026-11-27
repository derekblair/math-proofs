import PrefixBridge

namespace IU
def ClosedUnderPrefix (F : Finset (Finset Nat)) (n : Nat) : Prop :=
  ∀ B∈F, ∀ C ⊆ Finset.range n, C.card=B.card →
    (∀ i≤n, pr B i≤pr C i) → C∈F

def IsIU (F : Finset (Finset Nat)) (n p q : Nat) : Prop :=
  (∀ A∈F, A ⊆ Finset.range n) ∧
  ∀ A∈F, ∀ B∈F, p≤(A∩B).card ∧ (A∪B).card≤n-q

theorem prefix_compatible {F : Finset (Finset Nat)} {n p q : Nat}
    (hp : 0<p) (V : IsIU F n p q) (closed : ClosedUnderPrefix F n)
    {A B : Finset Nat} (aF : A∈F) (bF : B∈F) :
    ∃ t≤n, max p (A.card+B.card-(n-q))+t ≤ pr A t+pr B t := by
  classical
  let threshold := max p (A.card+B.card-(n-q))
  have pos : 0<threshold := hp.trans_le (Nat.le_max_left _ _)
  by_contra H
  have bounds (t : Nat) (ht : t≤n) : pr A t+pr B t≤t+(threshold-1) := by
    have no := fun h => H ⟨t,ht,h⟩
    change ¬ threshold+t ≤ _ at no
    omega
  obtain ⟨C,gC,cB,rank,intr⟩ := cap_intersection A B (V.1 A aF) (V.1 B bF) bounds
  have cF := closed B bF C gC cB rank
  obtain ⟨i,u⟩ := V.2 A aF C cF
  have hcard := Finset.card_union_add_card_inter A C
  rw [cB] at hcard
  dsimp [threshold] at intr
  omega

#print axioms prefix_compatible
end IU
