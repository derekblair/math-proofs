import NeutralAffine
import Mathlib.Tactic

namespace BalancedExact

theorem hit_neg (L : List ℤ) (c : ℤ) (p : 0<c)
    (unit : ∀ v ∈ L, v=1 ∨ v= -1) (fin : L.sum+c=0) :
    ∃ A B : List ℤ, L=A++(-1::B) ∧ A.sum+c=1 ∧ B.sum=0 := by
  induction L generalizing c with
  | nil => simp at fin; omega
  | cons x T ih =>
    have ut : ∀ v ∈ T, v=1 ∨ v= -1 := by
      intro v h
      exact unit v (List.mem_cons_of_mem _ h)
    have ux := unit x (List.mem_cons_self ..)
    have ht : T.sum+(c+x)=0 := by simp only [List.sum_cons] at fin; omega
    by_cases done : c+x=0
    · have xn : x= -1 := by rcases ux with h | h <;> omega
      refine ⟨[],T,?_,?_,?_⟩
      · simp [xn]
      · simp; omega
      · omega
    · have nn : 0<c+x := by rcases ux with h | h <;> omega
      obtain ⟨A,B,hh,ha,hb⟩ := ih (c+x) nn ut ht
      refine ⟨x::A,B,?_,?_,hb⟩
      · simp [hh]
      · simp only [List.sum_cons]; omega

theorem hit_pos (L : List ℤ) (c : ℤ) (p : c<0)
    (unit : ∀ v ∈ L, v=1 ∨ v= -1) (fin : L.sum+c=0) :
    ∃ A B : List ℤ, L=A++(1::B) ∧ A.sum+c= -1 ∧ B.sum=0 := by
  induction L generalizing c with
  | nil => simp at fin; omega
  | cons x T ih =>
    have ut : ∀ v ∈ T, v=1 ∨ v= -1 := by
      intro v h
      exact unit v (List.mem_cons_of_mem _ h)
    have ux := unit x (List.mem_cons_self ..)
    have ht : T.sum+(c+x)=0 := by simp only [List.sum_cons] at fin; omega
    by_cases done : c+x=0
    · have xp : x=1 := by rcases ux with h | h <;> omega
      refine ⟨[],T,?_,?_,?_⟩
      · simp [xp]
      · simp; omega
      · omega
    · have nn : c+x<0 := by rcases ux with h | h <;> omega
      obtain ⟨A,B,hh,ha,hb⟩ := ih (c+x) nn ut ht
      refine ⟨x::A,B,?_,?_,hb⟩
      · simp [hh]
      · simp only [List.sum_cons]; omega

theorem balanced_complete (L : List ℤ)
    (unit : ∀ v ∈ L, v=1 ∨ v= -1) (zero : L.sum=0) :
    NeutralAffine.Balanced L := by
  cases L with
  | nil => exact .nil
  | cons x T =>
    have ut : ∀ v ∈ T, v=1 ∨ v= -1 := by
      intro v h
      exact unit v (List.mem_cons_of_mem _ h)
    have ux := unit x (List.mem_cons_self ..)
    rcases ux with rfl | rfl
    · have ht : T.sum+1=0 := by simp only [List.sum_cons] at zero; omega
      obtain ⟨A,B,hh,ha,hb⟩ := hit_neg T 1 (by decide) ut ht
      have hA : A.length < (1::T).length := by simp [hh] <;> omega
      have hB : B.length < (1::T).length := by simp [hh] <;> omega
      have pa := balanced_complete A (fun v hv => ut v (by simp [hh,hv])) (by omega)
      have pb := balanced_complete B (fun v hv => ut v (by simp [hh,hv])) hb
      simpa [hh] using (NeutralAffine.Balanced.pos pa).append pb
    · have ht : T.sum+(-1)=0 := by simp only [List.sum_cons] at zero; omega
      obtain ⟨A,B,hh,ha,hb⟩ := hit_pos T (-1) (by decide) ut ht
      have hA : A.length < ((-1)::T).length := by simp [hh] <;> omega
      have hB : B.length < ((-1)::T).length := by simp [hh] <;> omega
      have pa := balanced_complete A (fun v hv => ut v (by simp [hh,hv])) (by omega)
      have pb := balanced_complete B (fun v hv => ut v (by simp [hh,hv])) hb
      simpa [hh] using (NeutralAffine.Balanced.neg pa).append pb
termination_by L.length
decreasing_by all_goals subst_vars; assumption

end BalancedExact

#print axioms BalancedExact.balanced_complete
