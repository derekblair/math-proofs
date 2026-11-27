import Compression

namespace IU
open scoped BigOperators

def mass (F : Sys) : Nat := ∑ A∈F, ∑ a∈A, a

private theorem move_mass {A : Bag} {i j : Nat}
    (h : eligible i j A) (lt : i<j) :
    (∑ a∈move i j A, a) < ∑ a∈A, a := by
  have U : i∉A.erase j := fun hh => h.1 (Finset.mem_of_mem_erase hh)
  rw [move,Finset.sum_insert U]
  have E := Finset.sum_erase_add _ (fun a : Nat => a) h.2
  omega

theorem compress_mass {F : Sys} {i j : Nat} (lt : i<j)
    {A : Bag} (a : A∈F) (movable : eligible i j A ∧ move i j A∉F) :
    mass (compress F i j)<mass F := by
  unfold mass compress
  rw [Finset.sum_image (action_inj F i j lt.ne)]
  apply Finset.sum_lt_sum
  · intro B b
    unfold action
    split
    · rename_i h
      exact (move_mass h.1 lt).le
    · exact le_rfl
  · exact ⟨A,a,by rw [action,if_pos movable]; exact move_mass movable.1 lt⟩

theorem stabilize (F : Sys) {n p q : Nat} (ok : IsIU F n p q) :
    ∃ H : Sys, H.card=F.card ∧ IsIU H n p q ∧ ElementaryClosed H n := by
  classical
  have main (m : Nat) : ∀ F : Sys, mass F = m → IsIU F n p q →
      ∃ H : Sys, H.card=F.card ∧ IsIU H n p q ∧ ElementaryClosed H n := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro F mF ok
      by_cases closed : ElementaryClosed F n
      · exact ⟨F,rfl,ok,closed⟩
      unfold ElementaryClosed at closed
      push Not at closed
      obtain ⟨A,a,i,j,lt,jn,iA,jA,M⟩ := closed
      have D : mass (compress F i j) < m := mF ▸ compress_mass lt a ⟨⟨iA,jA⟩,M⟩
      obtain ⟨H,ca,Hok,Hclosed⟩ := ih _ D _ rfl (compress_valid F ok lt jn)
      exact ⟨H,ca.trans (compress_card F i j lt.ne),Hok,Hclosed⟩
  exact main _ F rfl ok

#print axioms stabilize
end IU
