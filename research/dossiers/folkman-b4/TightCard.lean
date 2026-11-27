import RegularHall

namespace FolkmanB4.Tight
open Finset Critical
variable {L V : Type*} [Fintype L] [Fintype V]

def cutEdges (I : L → V → Prop) [DecidableRel I] (A : L → Bool) (B : V → Bool) :
    Finset (L × V) := univ.filter fun p => I p.1 p.2 ∧ A p.1≠B p.2

theorem signed_regular (I : L → V → Prop) [DecidableRel I] {k : Nat}
    (row : ∀ l, pts I l=k) (col : ∀ v, lns I v=k) (A : L → Bool) (B : V → Bool) :
    (∑ p∈cutEdges I A B, (bitZ (A p.1)-bitZ (B p.2))) =
      (k:Int)*((∑ l,bitZ (A l))-(∑ v,bitZ (B v))) := by
  classical
  have left (l : L) :
      (∑ v : V, if I l v then bitZ (A l) else 0)=(k:Int)*bitZ (A l) := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    change (pts I l:Int)*bitZ (A l)=(k:Int)*bitZ (A l)
    rw [row]
  have right (v : V) :
      (∑ l : L, if I l v then bitZ (B v) else 0)=(k:Int)*bitZ (B v) := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    change (lns I v:Int)*bitZ (B v)=(k:Int)*bitZ (B v)
    rw [col]
  unfold cutEdges
  rw [sum_filter,Fintype.sum_prod_type]
  have d (l : L) (v : V) :
      (if I l v ∧ A l≠B v then bitZ (A l)-bitZ (B v) else 0) =
        (if I l v then bitZ (A l) else 0)-(if I l v then bitZ (B v) else 0) := by
    by_cases h : I l v <;> by_cases e : A l=B v <;> simp [h,e]
  simp only [d,sum_sub_distrib]
  rw [sum_comm (f:=fun l v => if I l v then bitZ (B v) else 0)]
  simp only [left,right,←Finset.mul_sum,mul_sub]

theorem tight_cut_card (I : L → V → Prop) [DecidableRel I] [DecidableEq L]
    {k : Nat} (hk : 0<k) (row : ∀ l, pts I l=k) (col : ∀ v, lns I v=k)
    (A : L → Bool) (B : V → Bool)
    (tight : ∀ m : V ≃ L, (∀ j, I (m j) j) → ∃! j, A (m j)≠B j) :
    (cutEdges I A B).card=k := by
  classical
  obtain ⟨m,hm⟩ := regular_perfect_matching I hk row col
  obtain ⟨v,cv,uniq⟩ := tight m hm
  let b := bitZ (A (m v))-bitZ (B v)
  have bb : b≠0 := by
    unfold b
    cases x : A (m v) <;> cases y : B v <;> simp [x,y,bitZ] at cv ⊢
  have mass : (∑ l,bitZ (A l))-(∑ v,bitZ (B v))=b := by
    rw [←signed_cut_balance A B m]
    apply sum_eq_single v
    · intro u _ hu
      have z : A (m u)=B u := by
        by_contra ne
        exact hu (uniq u ne)
      simp [z]
    · simp
  have F : ∀ p∈cutEdges I A B, bitZ (A p.1)-bitZ (B p.2)=b := by
    intro p hp
    have q := (mem_filter.mp hp).2
    exact one_cut_direction I A B (fun a z h => regular_covers I row col h) tight q.1 (hm v) q.2 cv
  have s := signed_regular I row col A B
  rw [mass] at s
  rw [sum_congr rfl F,sum_const,nsmul_eq_mul] at s
  have j : ((cutEdges I A B).card:Int)=(k:Int) := mul_right_cancel₀ bb s
  exact_mod_cast j

#print axioms tight_cut_card
end FolkmanB4.Tight
