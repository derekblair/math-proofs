import TightDirections
import Mathlib.Combinatorics.Hall.Finite

namespace FolkmanB4.Tight
open Finset Critical

variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L]

def rows (I : L → V → Prop) [DecidableRel I] (c : V) : Finset L :=
  univ.filter fun l => I l c

/-- Counting regular incidences on any set of columns gives Hall's inequality. -/
theorem regular_hall (I : L → V → Prop) [DecidableRel I] {k : Nat} (hk : 0<k)
    (row : ∀ l, pts I l=k) (col : ∀ v, lns I v=k) (S : Finset V) :
    S.card ≤ (S.biUnion (rows I)).card := by
  classical
  let N := S.biUnion (rows I)
  have left (v : V) (hv : v∈S) : (∑ l∈N, if I l v then 1 else 0) = k := by
    rw [←sum_filter]
    have e : N.filter (fun l => I l v) = rows I v := by
      ext l
      constructor
      · intro h
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩
      · intro h
        have hi := (mem_filter.mp h).2
        exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨v,hv,h⟩,hi⟩
    rw [e]
    simpa [rows,lns] using col v
  have right (l : L) : (∑ v∈S, if I l v then 1 else 0) ≤ k := by
    rw [←sum_filter]
    have sub : S.filter (fun v => I l v) ⊆ (univ : Finset V).filter (fun v => I l v) :=
      filter_subset_filter _ (subset_univ _)
    simpa using (card_le_card sub).trans (le_of_eq (row l))
  have c : S.card*k≤N.card*k := calc
    _ = ∑ v∈S, k := by simp
    _ = ∑ v∈S, ∑ l∈N, if I l v then 1 else 0 :=
      sum_congr rfl fun v hv => (left v hv).symm
    _ = ∑ l∈N, ∑ v∈S, if I l v then 1 else 0 := sum_comm
    _ ≤ ∑ l∈N, k := sum_le_sum fun l _ => right l
    _ = _ := by simp
  exact Nat.le_of_mul_le_mul_right c hk

theorem regular_perfect_matching (I : L → V → Prop) [DecidableRel I] {k : Nat}
    (hk : 0<k) (row : ∀ l, pts I l=k) (col : ∀ v, lns I v=k) :
    ∃ m : V ≃ L, ∀ v, I (m v) v := by
  classical
  obtain ⟨f,inj,hf⟩ :=
    (all_card_le_biUnion_card_iff_existsInjective' (rows I)).mp (regular_hall I hk row col)
  have c := counts I
  simp only [row,col,sum_const,card_univ,nsmul_eq_mul] at c
  change Fintype.card L*k=Fintype.card V*k at c
  have eq : Fintype.card V=Fintype.card L :=
    (Nat.eq_of_mul_eq_mul_right hk c).symm
  let m := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,eq⟩)
  exact ⟨m,fun v => (mem_filter.mp (hf v)).2⟩

theorem regular_covers (I : L → V → Prop) [DecidableRel I] {k : Nat}
    (row : ∀ l, pts I l=k) (col : ∀ v, lns I v=k) {l : L} {v : V} (e : I l v) :
    ∃ m : V ≃ L, m v=l ∧ ∀ u, I (m u) u := by
  classical
  induction k generalizing I with
  | zero =>
    have nz : 0<pts I l := card_pos.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,e⟩⟩
    simp [row l] at nz
  | succ k ih =>
    obtain ⟨m,hm⟩ := regular_perfect_matching I (Nat.succ_pos k) row col
    by_cases yes : m v=l
    · exact ⟨m,yes,hm⟩
    let J (a : L) (b : V) := I a b ∧ m b≠a
    let _ : DecidableRel J := fun a b => inferInstanceAs (Decidable (I a b ∧ m b≠a))
    have r (a : L) : pts J a=k := by
      have E : (univ.filter fun b => J a b)=((univ : Finset V).filter fun b => I a b).erase (m.symm a) := by
        ext b
        simp only [mem_filter,mem_univ,true_and,mem_erase,J]
        have z : b=m.symm a ↔ m b=a := by
          constructor
          · intro h; rw [h,m.apply_symm_apply]
          · intro h; exact m.injective (h.trans (m.apply_symm_apply a).symm)
        simp [z,and_comm]
      have hh : m.symm a ∈ (univ.filter fun b => I a b) := by simpa using hm (m.symm a)
      unfold pts
      rw [E,card_erase_of_mem hh]
      exact Nat.succ_sub_one k ▸ congrArg (·-1) (row a)
    have c (b : V) : lns J b=k := by
      have E : (univ.filter fun a => J a b)=((univ : Finset L).filter fun a => I a b).erase (m b) := by
        ext a
        simp only [mem_filter,mem_univ,true_and,mem_erase,J]
        exact ⟨fun x => ⟨Ne.symm x.2,x.1⟩,fun x => ⟨x.2,Ne.symm x.1⟩⟩
      have hh : m b ∈ (univ.filter fun a => I a b) := mem_filter.mpr ⟨mem_univ _,hm b⟩
      unfold lns
      rw [E,card_erase_of_mem hh]
      exact Nat.succ_sub_one k ▸ congrArg (·-1) (col b)
    have ej : J l v := ⟨e,yes⟩
    obtain ⟨n,nv,h⟩ := ih J r c ej
    exact ⟨n,nv,fun u => (h u).1⟩

#print axioms regular_covers
end FolkmanB4.Tight
