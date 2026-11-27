import LubellCylinder

namespace IU.Lubell
open scoped BigOperators

def opposite (F : Family) (n : Nat) : Family :=
  F.image (fun A => Finset.range n \ A)

theorem opp_valid {F : Family} {n t u : Nat} (h : IsIU F n t u) (un : u≤n) :
    IsIU (opposite F n) n u t := by
  classical
  refine ⟨?_,?_⟩
  · intro X x
    obtain ⟨A,a,rfl⟩ := Finset.mem_image.mp x
    exact Finset.sdiff_subset
  · intro X x Y y
    obtain ⟨A,a,rfl⟩ := Finset.mem_image.mp x
    obtain ⟨B,b,rfl⟩ := Finset.mem_image.mp y
    have e : (Finset.range n \ A) ∩ (Finset.range n \ B) = Finset.range n \ (A∪B) := by
      ext z
      simp only [Finset.mem_inter,Finset.mem_sdiff,Finset.mem_union]
      tauto
    have f : (Finset.range n \ A) ∪ (Finset.range n \ B) = Finset.range n \ (A∩B) := by
      ext z
      simp only [Finset.mem_inter,Finset.mem_sdiff,Finset.mem_union]
      tauto
    rw [e,f,Finset.card_sdiff_of_subset (Finset.union_subset (h.1 A a) (h.1 B b)),
      Finset.card_sdiff_of_subset (Finset.inter_subset_left.trans (h.1 A a)),
      Finset.card_range]
    have z := h.2 A a B b
    have hk := h.2 A a A a
    simp only [Finset.union_self] at hk
    omega

theorem weight_symm {n k : Nat} (h : k≤n) : weight n (n-k)=weight n k := by
  unfold weight
  rw [show n-(n-k)=k by omega,mul_comm]

theorem opp_score {F : Family} {n t u : Nat} (h : IsIU F n t u) :
    score n (opposite F n)=score n F := by
  classical
  have CC (A : Finset Nat) (a : A∈F) : Finset.range n \ (Finset.range n \ A)=A := by
    ext z
    simp only [Finset.mem_sdiff]
    have L : z∈A → z∈Finset.range n := fun hz => h.1 A a hz
    tauto
  have I : Set.InjOn (fun A => Finset.range n \ A) ↑F := by
    intro A a B b E
    have K := congrArg (fun g => Finset.range n \ g) E
    rwa [CC A a,CC B b] at K
  unfold score opposite
  rw [Finset.sum_image I]
  apply Finset.sum_congr rfl
  intro A a
  rw [Finset.card_sdiff_of_subset (h.1 A a),Finset.card_range]
  exact weight_symm (by simpa using Finset.card_le_card (h.1 A a))

theorem proposed_score {n t u : Nat} (h : t+u≤n) :
    score n (proposed n t u)=weight (t+u) t := by
  have s := cylinder_score t u (n-(t+u))
  rw [Nat.add_sub_of_le h] at s
  rwa [proposed_eq h]

theorem proposed_symm {n t u : Nat} (h : t+u≤n) :
    score n (proposed n t u)=score n (proposed n u t) := by
  rw [proposed_score h,proposed_score (by omega : u+t≤n)]
  rw [Nat.add_comm u t]
  have e := weight_symm (n:=t+u) (k:=t) (by omega)
  rw [show t+u-t=u by omega] at e
  exact e.symm

theorem proposed_fails {n t u : Nat} (large : 2≤max t u) (bound : t+u+2≤n) :
    ∃ F : Family, IsIU F n t u ∧ score n (proposed n t u)<score n F := by
  by_cases le : t≤u
  · exact proposed_fails_of_le t u n le (by omega) bound
  · obtain ⟨F,V,D⟩ := proposed_fails_of_le u t n (by omega) (by omega) (by omega)
    exact ⟨opposite F n,opp_valid V (by omega),by rwa [opp_score V,proposed_symm (by omega)]⟩

#print axioms proposed_fails
end IU.Lubell
