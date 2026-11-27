import FamilyPrefix

namespace IU

def double (F : Finset (Finset Nat)) (n : Nat) :=
  F ∪ F.image (fun A => insert n A)

theorem lift_double {n p q : Nat} (F : Finset (Finset Nat)) (ok : IsIU F n p q) (qn : q≤n) :
    IsIU (double F n) (n+1) p q ∧ (double F n).card=2*F.card := by
  have w (A : Finset Nat) (h : A∈double F n) :
      ∃ X∈F, X⊆A ∧ A⊆insert n X := by
    rcases Finset.mem_union.mp h with a|a
    · exact ⟨A,a,(fun _ hx => hx),Finset.subset_insert _ _⟩
    · obtain ⟨X,xF,rfl⟩ := Finset.mem_image.mp a
      exact ⟨X,xF,Finset.subset_insert _ _,(fun _ hx => hx)⟩
  have no (A : Finset Nat) (a : A∈F) : n∉A :=
    fun h => (Nat.lt_irrefl _ (Finset.mem_range.mp (ok.1 A a h)))
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro A a x xx
    obtain ⟨X,xF,_,subset⟩ := w A a
    rcases Finset.mem_insert.mp (subset xx) with rfl|m
    · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (ok.1 X xF m)))
  · intro A a B b
    obtain ⟨X,xF,xa,ax⟩ := w A a
    obtain ⟨Y,yF,yb,by_⟩ := w B b
    obtain ⟨pc,qc⟩ := ok.2 X xF Y yF
    have it := Finset.card_le_card (Finset.inter_subset_inter xa yb)
    have un := Finset.card_le_card (Finset.union_subset_union ax by_)
    have e : insert n X ∪ insert n Y = insert n (X∪Y) := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_union]
      grind
    rw [e,Finset.card_insert_of_notMem] at un
    · exact ⟨pc.trans it,by omega⟩
    · simp [no X xF,no Y yF]
  · have inj : Set.InjOn (fun A : Finset Nat => insert n A) ↑F := by
      intro A a B b e
      have E := congrArg (fun X : Finset Nat => X.erase n) e
      simpa [Finset.erase_insert,no A a,no B b] using E
    have dis : Disjoint F (F.image (fun A => insert n A)) := Finset.disjoint_left.mpr (by
      intro A a b
      obtain ⟨X,xF,rfl⟩ := Finset.mem_image.mp b
      exact no _ a (Finset.mem_insert_self _ _))
    unfold double
    rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injOn inj]
    omega

#print axioms lift_double
end IU
