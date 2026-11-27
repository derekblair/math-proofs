import LubellCounterexample
import Mathlib.Data.Finset.Powerset

namespace IU.Lubell

theorem mem_cylinder {t u d : Nat} {A : Finset Nat} :
    A∈cylinder t u d ↔
      A⊆Finset.range (t+u+d) ∧ Finset.range t⊆A ∧ ∀ i∈A, i<t ∨ t+u≤i := by
  classical
  induction d generalizing A with
  | zero =>
    constructor
    · intro h
      have eq : A=Finset.range t := by simpa [cylinder] using h
      rw [eq]
      refine ⟨?_,fun _ h=>h,fun i hi=>Or.inl (Finset.mem_range.mp hi)⟩
      intro i hi
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
    · intro ⟨outer,inner,forbid⟩
      have h : A ⊆ Finset.range t := by
        intro i hi
        have lo := Finset.mem_range.mp (outer hi)
        exact Finset.mem_range.mpr (by rcases forbid i hi with H|H <;> omega)
      have e := Finset.Subset.antisymm h inner
      simpa [cylinder] using e
  | succ d ih =>
    let n := t+u+d
    change A∈double (cylinder t u d) n ↔
      A⊆Finset.range (n+1) ∧ Finset.range t⊆A ∧ ∀ i∈A, i<t ∨ t+u≤i
    constructor
    · intro h
      rcases Finset.mem_union.mp h with m|m
      · obtain ⟨out,inside,loc⟩ := ih.mp m
        refine ⟨?_,inside,loc⟩
        intro i hi
        exact Finset.mem_range.mpr ((Finset.mem_range.mp (out hi)).trans (Nat.lt_succ_self n))
      · obtain ⟨B,b,rfl⟩ := Finset.mem_image.mp m
        obtain ⟨out,inside,loc⟩ := ih.mp b
        refine ⟨?_,inside.trans (Finset.subset_insert _ _),?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl|mi
          · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
          · exact Finset.mem_range.mpr ((Finset.mem_range.mp (out mi)).trans (Nat.lt_succ_self n))
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl|mi
          · exact Or.inr (by dsimp [n]; omega)
          · exact loc i mi
    · intro ⟨out,inside,loc⟩
      by_cases H : n∈A
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨A.erase n,ih.mpr ⟨?_,?_,?_⟩,Finset.insert_erase H⟩
        · intro i hi
          obtain ⟨ne,ha⟩ := Finset.mem_erase.mp hi
          have I := Finset.mem_range.mp (out ha)
          exact Finset.mem_range.mpr (by omega)
        · intro i hi
          refine Finset.mem_erase.mpr ⟨?_,inside hi⟩
          have z := Finset.mem_range.mp hi
          dsimp [n]
          omega
        · exact fun i hi => loc i (Finset.mem_erase.mp hi).2
      · apply Finset.mem_union_left
        apply ih.mpr
        refine ⟨?_,inside,loc⟩
        intro i hi
        have H' : i≠n := fun e => H (e ▸ hi)
        have I := Finset.mem_range.mp (out hi)
        exact Finset.mem_range.mpr (by omega)

def proposed (n t u : Nat) : Family :=
  (Finset.range n).powerset.filter (fun A =>
    Finset.range t⊆A ∧ ∀ i∈A, i<t ∨ t+u≤i)

theorem proposed_eq {n t u : Nat} (h : t+u≤n) :
    proposed n t u=cylinder t u (n-(t+u)) := by
  ext A
  rw [mem_cylinder,Nat.add_sub_of_le h]
  simp [proposed]

theorem proposed_fails_of_le (t u n : Nat) (le : t≤u) (ut : 2≤u) (hn : t+u+2≤n) :
    ∃ F : Family, IsIU F n t u ∧ score n (proposed n t u)<score n F := by
  rw [proposed_eq (by omega)]
  exact eventual_counterexample t u n le ut hn

theorem proposed_fails_two (n : Nat) (h : 6≤n) :
    ∃ F : Family, IsIU F n 2 2 ∧ score n (proposed n 2 2)<score n F :=
  proposed_fails_of_le 2 2 n (by decide) (by decide) h

#print axioms proposed_fails_two
end IU.Lubell
