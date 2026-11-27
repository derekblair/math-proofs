import TightMinContract
import TightCard

namespace FolkmanB4.Tight
open Finset Critical
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

theorem contraction_size (I : L → V → Prop) [DecidableRel I]
    (S : Finset L) (T : Finset V)
    (large : Nontrivial S T)
    (inward : Inward I (fun l => decide (l∈S)) (fun v => decide (v∈T)))
    (tight : Tight I (fun l => decide (l∈S)) (fun v => decide (v∈T)))
    (col : ∀ v, lns I v = 3)
    (M : ∃ m : V ≃ L, ∀ v, I (m v) v) :
    3 ≤ Fintype.card (In (fun l => decide (l∈S))) ∧
    3 ≤ Fintype.card (Option (In (fun v => decide (v∈T)))) := by
  obtain ⟨m,hm⟩ := M
  obtain ⟨q,_,_⟩ := project_original I _ _ inward tight m hm
  have eq := Fintype.card_congr q
  rw [Fintype.card_option,card_inside,card_inside] at eq
  have size := large.1
  unfold shore at size
  have pos : 0<T.card := by omega
  obtain ⟨v,hv⟩ := card_pos.mp pos
  have sub : (univ.filter fun l => I l v) ⊆ S := by
    intro l hl
    exact of_decide_eq_true (inward l v (mem_filter.mp hl).2 (by simp [hv]))
  have c := card_le_card sub
  change lns I v ≤ S.card at c
  rw [col] at c
  rw [Fintype.card_option,card_inside,card_inside]
  omega

theorem no_small_cut_degree (I : L → V → Prop) [DecidableRel I] (H : NoSmallCut I)
    (M : ∃ m : V ≃ L, ∀ v, I (m v) v) (n : 3≤Fintype.card V) (v : V) :
    3 ≤ lns I v := by
  simpa [lns,rows] using robust_hall I H M ({v} : Finset V) (by simp) (by simpa using n)

#print axioms contraction_size
#print axioms no_small_cut_degree
end FolkmanB4.Tight
