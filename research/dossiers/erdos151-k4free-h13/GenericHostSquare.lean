import HostSquareData

namespace Erdős151.H12.Wagner
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]

/-- In a cyclic ordered square, each unordered successive pair is different. -/
private theorem pair_step_inj (x : Fin 4 → V) (hi : Function.Injective x) :
    Function.Injective (fun i => ({x i,x (i+1)} : Finset V)) := by
  intro i j he
  change ({x i,x (i+1)} : Finset V) = {x j,x (j+1)} at he
  have hm : x i ∈ ({x j,x (j+1)} : Finset V) := by rw [← he]; simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with h|h
  · exact hi h
  · have h1 := hi h
    have ht : x (i+1) ∈ ({x j,x (j+1)} : Finset V) := by rw [← he]; simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    have impossible : ∀ a b : Fin 4, a=b+1 → a+1≠b ∧ a+1≠b+1 := by decide
    exact False.elim (ht.elim (fun h => (impossible i j h1).1 (hi h))
      (fun h => (impossible i j h1).2 (hi h)))

private theorem two_sub_three (A : Finset V) (v x y : V)
    (hc : A.card=2) (sub : A ⊆ {v,x,y}) :
    A={v,x} ∨ A={v,y} ∨ A={x,y} := by
  obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp hc
  have ha := sub (show a∈({a,b}:Finset V) by simp)
  have hb := sub (show b∈({a,b}:Finset V) by simp)
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
    first | exact False.elim (ab rfl)
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
          | exact Or.inl (Finset.pair_comm _ _)
          | exact Or.inr (Or.inl (Finset.pair_comm _ _))
          | exact Or.inr (Or.inr (Finset.pair_comm _ _))

variable {L R : Type*} [Fintype V] [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- Four genuine link edges and a complete triangle roster give the exact
ordered square incidence shape; no global local-link isomorphism is used. -/
theorem square_data_of_cycle {E : L ↪ Finset V} {Tr : R ↪ Finset V}
    (e2 : ∀ e, (E e).card=2) (v : V) (x : Fin 4 → V)
    (xi : Function.Injective x) (xv : ∀ i, x i ≠ v)
    (sp : ∀ i, hostRel E v (x i))
    (ri : ∀ i, hostRel E (x i) (x (i+1)))
    (tri : ∀ i, ∃ t, Tr t = {v,x i,x (i+1)}) :
    ∃ (spoke : Fin 4 → L) (tr : Fin 4 → R) (outside : Fin 4 → L),
      Function.Injective spoke ∧ Function.Injective tr ∧ Function.Injective outside ∧
      (∀ i, hostIncEdge E Tr (tr i) = {spoke i,spoke (i+1),outside i}) ∧
      v ∈ E (spoke 0) := by
  classical
  have set_of_members {a b : V} (ne : a ≠ b) {e : L} (ha : a ∈ E e) (hb : b ∈ E e) :
      E e = {a,b} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro y hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with rfl|rfl
      · exact ha
      · exact hb
    · rw [e2]
      simp [ne]
  let spoke := fun i => Classical.choose (sp i)
  have sq (i : Fin 4) : E (spoke i)={v,x i} :=
    set_of_members (xv i).symm (Classical.choose_spec (sp i)).1 (Classical.choose_spec (sp i)).2
  let tr := fun i => Classical.choose (tri i)
  have tq (i : Fin 4) : Tr (tr i)={v,x i,x (i+1)} :=
    Classical.choose_spec (tri i)
  let outside := fun i : Fin 4 => Classical.choose (ri i)
  have oq (i : Fin 4) : E (outside i)={x i,x (i+1)} := by
    have hi : i ≠ i+1 := (show ∀ k:Fin 4, k≠k+1 by decide) i
    exact set_of_members (fun h => hi (xi h))
      (Classical.choose_spec (ri i)).1 (Classical.choose_spec (ri i)).2
  refine ⟨spoke,tr,outside,?_,?_,?_,?_,?_⟩
  · intro i j h
    have hm : x i ∈ E (spoke j) := by rw [←h,sq]; simp
    rw [sq] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    exact xi (hm.resolve_left (xv i))
  · intro i j h
    have he : (Tr (tr i)).erase v = (Tr (tr j)).erase v := by rw [h]
    rw [tq,tq] at he
    rw [Finset.erase_insert (by simp [(xv i).symm,(xv (i+1)).symm]),
      Finset.erase_insert (by simp [(xv j).symm,(xv (j+1)).symm])] at he
    exact pair_step_inj x xi he
  · intro i j h
    have he := congrArg E h
    rw [oq,oq] at he
    exact pair_step_inj x xi he
  · intro i
    ext e
    simp only [hostIncEdge,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro hs
      rw [tq] at hs
      rcases two_sub_three (E e) v (x i) (x (i+1)) (e2 e) hs with h|h|h
      · exact Or.inl (E.injective (h.trans (sq i).symm))
      · exact Or.inr (Or.inl (E.injective (h.trans (sq (i+1)).symm)))
      · exact Or.inr (Or.inr (E.injective (h.trans (oq i).symm)))
    · rintro (rfl|rfl|rfl) <;> rw [tq]
      · rw [sq]; simp
      · rw [sq]; simp
      · rw [oq]; simp
  · rw [sq]; simp

#print axioms square_data_of_cycle
end Erdős151.H12.Wagner
