import HaarHalfCollision

namespace HaarWordExtension
open HaarSharpCore (good)
open HaarHalfCollision

theorem snoc_good (L : List (Fin 3)) (j : Fin 3)
    (g : good L = true) (h : L.getLast? ≠ some j) :
    good (L++[j]) = true := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases L with
    | nil =>
      have hh : a ≠ j := by simpa using h
      simp [good,hh]
    | cons b T =>
      have hg : a ≠ b ∧ good (b::T)=true := by simpa [good] using g
      have ht : (b::T).getLast? ≠ some j := by simpa using h
      have he := ih hg.2 ht
      simpa [good,hg.1] using he

theorem common_next (L R : List (Fin 3)) :
    ∃ j : Fin 3, L.getLast? ≠ some j ∧ R.getLast? ≠ some j := by
  generalize L.getLast? = l
  generalize R.getLast? = r
  revert l r
  decide

variable {G : Type*} [Group G]

theorem prod_snoc (x y : G) (b : ℕ) (L : List (Fin 3)) (j : Fin 3) :
    prodFrom x y b (L++[j]) = prodFrom x y b L * signPort x y (b+L.length) j := by
  induction L generalizing b with
  | nil => simp [prodFrom]
  | cons a L ih =>
    simp only [List.cons_append,prodFrom,ih,List.length_cons,mul_assoc]
    rw [show b+1+L.length=b+(L.length+1) by omega]

theorem extend (x y : G) (d k : ℕ) (L R : List (Fin 3)) (ll : L.length=k) (rl : R.length=k)
    (gl : good L = true) (gr : good R = true) (ne : L ≠ R)
    (e : prodFrom x y 0 L = prodFrom x y 0 R) :
    ∃ L' R' : List (Fin 3), L'.length=k+d ∧ R'.length=k+d ∧
      good L'=true ∧ good R'=true ∧ L'≠R' ∧ prodFrom x y 0 L'=prodFrom x y 0 R' := by
  induction d generalizing k L R with
  | zero => exact ⟨L,R,by simpa,by simpa,gl,gr,ne,e⟩
  | succ d ih =>
    obtain ⟨j,hl,hr⟩ := common_next L R
    obtain ⟨A,B,al,bl,ag,bg,neq,peq⟩ := ih (k+1) (L++[j]) (R++[j])
      (by simp [ll]) (by simp [rl]) (snoc_good L j gl hl) (snoc_good R j gr hr)
      (fun he => ne (List.append_cancel_right he))
      (by rw [prod_snoc,prod_snoc,ll,rl,e])
    exact ⟨A,B,by omega,by omega,ag,bg,neq,peq⟩

end HaarWordExtension
#print axioms HaarWordExtension.extend
