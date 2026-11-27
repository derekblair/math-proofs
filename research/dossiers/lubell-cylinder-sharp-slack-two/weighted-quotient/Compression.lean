import ShiftReach
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Basic

namespace IU
abbrev Bag := Finset Nat
abbrev Sys := Finset Bag
def move (i j : Nat) (A : Bag) : Bag := insert i (A.erase j)
def eligible (i j : Nat) (A : Bag) : Prop := i∉A ∧ j∈A
instance (i j : Nat) (A : Bag) : Decidable (eligible i j A) := by unfold eligible; infer_instance

def action (F : Sys) (i j : Nat) (A : Bag) : Bag :=
  if eligible i j A ∧ move i j A ∉ F then move i j A else A

def compress (F : Sys) (i j : Nat) : Sys := F.image (action F i j)

def swap (i j : Nat) (A : Bag) : Bag := A.map (Equiv.swap i j).toEmbedding

private theorem swap_mem (i j x : Nat) (A : Bag) :
    x∈swap i j A ↔ Equiv.swap i j x ∈ A := by
  simp [swap]

private theorem swap_of_eligible {i j : Nat} (ne : i≠j) {A : Bag} (h : eligible i j A) :
    swap i j A = move i j A := by
  ext x
  rw [swap_mem]
  by_cases xi : x=i
  · subst x
    simp [move,h.2]
  by_cases xj : x=j
  · subst x
    simp [move,ne.symm,h.1]
  · simp [move,xi,xj,Equiv.swap_apply_of_ne_of_ne xi xj]

private theorem swap_neutral {i j : Nat} {A : Bag} (h : i∈A ↔ j∈A) :
    swap i j A=A := by
  ext x
  rw [swap_mem]
  by_cases xi : x=i
  · subst x
    simpa using h.symm
  by_cases xj : x=j
  · subst x
    simpa using h
  · rw [Equiv.swap_apply_of_ne_of_ne xi xj]

private theorem swap_invol (i j : Nat) (A : Bag) :
    swap i j (swap i j A)=A := by
  ext x
  rw [swap_mem,swap_mem,Equiv.swap_apply_self]

private theorem swap_bounds (i j n p q : Nat) (A B : Bag)
    (h : p≤(A∩B).card ∧ (A∪B).card≤n-q) :
    p≤(swap i j A∩swap i j B).card ∧ (swap i j A∪swap i j B).card≤n-q := by
  simpa only [swap,←Finset.map_inter,←Finset.map_union,Finset.card_map] using h

theorem action_inj (F : Sys) (i j : Nat) (ne : i≠j) :
    Set.InjOn (action F i j) ↑F := by
  intro A hA B hB E
  have aF : A∈F := hA
  have bF : B∈F := hB
  unfold action at E
  split_ifs at E with a b b
  · rw [←swap_of_eligible ne a.1,←swap_of_eligible ne b.1] at E
    simpa only [swap_invol] using congrArg (swap i j) E
  · exact False.elim (a.2 (E.symm ▸ bF))
  · exact False.elim (b.2 (E ▸ aF))
  · exact E

theorem compress_card (F : Sys) (i j : Nat) (ne : i≠j) :
    (compress F i j).card=F.card := Finset.card_image_of_injOn (action_inj F i j ne)

private theorem move_bounded {n i j : Nat} (in_ : i<n) {A : Bag} (h : A⊆Finset.range n) :
    move i j A⊆Finset.range n := by
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl|e
  · exact Finset.mem_range.mpr in_
  · exact h (Finset.mem_of_mem_erase e)

private theorem one_change {n p q i j : Nat} (F : Sys)
    (V : IsIU F n p q) (ne : i≠j) {A B : Bag} (aF : A∈F) (bF : B∈F)
    (a : eligible i j A) (unmoved : ¬(eligible i j B ∧ move i j B ∉ F)) :
    p≤(move i j A∩B).card ∧ (move i j A∪B).card≤n-q := by
  by_cases ib : i∈B <;> by_cases jb : j∈B
  · have N : i∈B ↔ j∈B := iff_of_true ib jb
    simpa only [swap_of_eligible ne a,swap_neutral N] using
      swap_bounds i j n p q A B (V.2 A aF B bF)
  · obtain ⟨pA,uA⟩ := V.2 A aF B bF
    have I : A∩B ⊆ move i j A∩B := by
      intro z hz
      obtain ⟨za,zb⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun e => jb (e ▸ zb),za⟩),zb⟩
    have U : move i j A∪B ⊆ A∪B := by
      intro z hz
      rcases Finset.mem_union.mp hz with hp|hp
      · rcases Finset.mem_insert.mp hp with zz|zz
        · exact Finset.mem_union.mpr (Or.inr (zz.symm ▸ ib))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_of_mem_erase zz))
      · exact Finset.mem_union.mpr (Or.inr hp)
    exact ⟨pA.trans (Finset.card_le_card I),(Finset.card_le_card U).trans uA⟩
  · have h : eligible i j B := ⟨ib,jb⟩
    have f : move i j B ∈ F := by
      by_contra n
      exact unmoved ⟨h,n⟩
    have P := swap_bounds i j n p q A (move i j B) (V.2 A aF _ f)
    rw [←swap_of_eligible ne h,swap_invol,swap_of_eligible ne a] at P
    exact P
  · have N : i∈B ↔ j∈B := iff_of_false ib jb
    simpa only [swap_of_eligible ne a,swap_neutral N] using
      swap_bounds i j n p q A B (V.2 A aF B bF)

theorem compress_valid {n p q i j : Nat} (F : Sys) (V : IsIU F n p q)
    (hij : i<j) (jn : j<n) : IsIU (compress F i j) n p q := by
  refine ⟨?_,?_⟩
  · intro T tF
    obtain ⟨A,aF,rfl⟩ := Finset.mem_image.mp tF
    unfold action
    split
    · exact move_bounded (hij.trans jn) (V.1 _ aF)
    · exact V.1 _ aF
  · intro T tF U uF
    obtain ⟨A,aF,rfl⟩ := Finset.mem_image.mp tF
    obtain ⟨B,bF,rfl⟩ := Finset.mem_image.mp uF
    unfold action
    split_ifs with za zb zb
    · simpa only [swap_of_eligible hij.ne za.1,swap_of_eligible hij.ne zb.1] using
        swap_bounds i j n p q A B (V.2 A aF B bF)
    · exact one_change F V hij.ne aF bF za.1 zb
    · simpa only [Finset.inter_comm,Finset.union_comm] using
        one_change F V hij.ne bF aF zb.1 za
    · exact V.2 A aF B bF

#print axioms compress_valid
#print axioms compress_card
end IU
