import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace ZFChain
open Finset

variable {V I E : Type*} [DecidableEq V] [DecidableEq I] [DecidableEq E]

/-- Sequential application of the ordinary color-change rule. -/
def CanForce (A : V → V → Prop) (B : Finset V) (x y : V) : Prop :=
  x ∈ B ∧ y ∉ B ∧ A x y ∧ ∀ z, A x z → z ∉ B → z = y

inductive Reach (A : V → V → Prop) (S : Finset V) : Finset V → Prop
  | zero : Reach A S S
  | step {B : Finset V} {x y : V} :
      Reach A S B → CanForce A B x y → Reach A S (insert y B)

/-- A local fort is tested with the vertices and edges of just one block. -/
def BlockFort (A : V → V → Prop) (block : V → I) (i : I) (F : Finset V) : Prop :=
  F.Nonempty ∧ (∀ y ∈ F, block y = i) ∧
    ∀ x, block x = i → x ∉ F → ∀ y ∈ F, A x y →
        ∃ z ∈ F, A x z ∧ z ≠ y

/-- Bridge endpoints for each interface. The crossing forces must use one of these edges. -/
theorem trackBridges (A : V → V → Prop) (block : V → I) (l r : E → V)
    (hcross : ∀ x y, A x y → block x ≠ block y →
       ∃ e, (x = l e ∧ y = r e) ∨ (x = r e ∧ y = l e))
    (S B : Finset V) (h : Reach A S B) :
    ∃ D : Finset V, ∃ U : Finset E, D.card ≤ U.card ∧
      (∀ e ∈ U, l e ∈ B ∧ r e ∈ B) ∧
      (∀ i F, BlockFort A block i F →
        Disjoint F (S ∪ D) → Disjoint F B) := by
  induction h with
  | zero =>
      refine ⟨∅, ∅, by simp, by simp, ?_⟩
      simpa
  | @step B x y _ hc ih =>
      obtain ⟨D,U,hd,hu,hf⟩ := ih
      obtain ⟨hx, hy, ha, hun⟩ := hc
      by_cases heq : block x = block y
      · refine ⟨D,U,hd,?_,?_⟩
        · intro e he
          exact ⟨mem_insert_of_mem (hu e he).1,mem_insert_of_mem (hu e he).2⟩
        · intro i F hF hs
          have hb := hf i F hF hs
          rw [disjoint_left] at hb ⊢
          intro z hz hz'
          rcases mem_insert.mp hz' with rfl | hz'
          · have hxF : x ∉ F := fun hh => hb hh hx
            have hbxi : block x = i := heq.trans (hF.2.1 _ hz)
            obtain ⟨v,hv,hav,hne⟩ := hF.2.2 x hbxi hxF z hz ha
            exact hne (hun v hav (hb hv))
          · exact hb hz hz'
      · obtain ⟨e,he⟩ := hcross x y ha heq
        have hen : e ∉ U := by
          intro hu'
          rcases he with ⟨_,hr⟩ | ⟨_,hl⟩
          · exact hy (hr ▸ (hu e hu').2)
          · exact hy (hl ▸ (hu e hu').1)
        refine ⟨insert y D, insert e U, ?_, ?_, ?_⟩
        · rw [card_insert_of_notMem hen]
          exact (card_insert_le _ _).trans (Nat.succ_le_succ hd)
        · intro e' h'
          rcases mem_insert.mp h' with rfl | h'
          · rcases he with ⟨hl,hr⟩ | ⟨hr,hl⟩
            · exact ⟨hl ▸ mem_insert_of_mem hx,hr ▸ mem_insert_self _ _⟩
            · exact ⟨hl ▸ mem_insert_self _ _,hr ▸ mem_insert_of_mem hx⟩
          · exact ⟨mem_insert_of_mem (hu e' h').1,mem_insert_of_mem (hu e' h').2⟩
        · intro i F hF hs
          have hs' : Disjoint F (S ∪ D) := by
            apply disjoint_of_subset_right _ hs
            intro v hv
            rcases mem_union.mp hv with hh | hh
            · exact mem_union_left _ hh
            · exact mem_union_right _ (mem_insert_of_mem hh)
          have hb := hf i F hF hs'
          rw [disjoint_left] at hb hs ⊢
          intro z hz hz'
          rcases mem_insert.mp hz' with rfl | hz'
          · exact hs hz (mem_union_right _ (mem_insert_self _ _))
          · exact hb hz hz'

theorem forceLower [Fintype V] [Fintype I] [Fintype E]
    (A : V → V → Prop) (block : V → I) (l r : E → V) (p : ℕ)
    (cross : ∀ x y, A x y → block x ≠ block y →
       ∃ e, (x = l e ∧ y = r e) ∨ (x = r e ∧ y = l e))
    (localSmall : ∀ (i : I) (S : Finset V), (S.filter (fun y => block y = i)).card < p →
       ∃ F, BlockFort A block i F ∧ Disjoint F S)
    (S : Finset V) (hs : Reach A S univ) :
    p * Fintype.card I ≤ S.card + Fintype.card E := by
  obtain ⟨D,U,hd,_,hf⟩ := trackBridges A block l r cross S univ hs
  have hfib : ∀ i : I, p ≤ ((S ∪ D).filter (fun y => block y = i)).card := by
    intro i
    by_contra h
    obtain ⟨F,hF,hdj⟩ := localSmall i (S ∪ D) (by omega)
    have hdd := hf i F hF hdj
    obtain ⟨y,hy⟩ := hF.1
    exact (disjoint_left.mp hdd) hy (mem_univ y)
  have ht : ∑ i : I, ((S ∪ D).filter (fun y => block y = i)).card = (S ∪ D).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have hb := Finset.sum_le_sum (s := (univ : Finset I)) (fun i _ => hfib i)
  simp only [sum_const, card_univ, nsmul_eq_mul, ht] at hb
  calc
    p * Fintype.card I = Fintype.card I * p := Nat.mul_comm _ _
    _ ≤ (S ∪ D).card := hb
    _ ≤ S.card + D.card := card_union_le _ _
    _ ≤ S.card + Fintype.card E := Nat.add_le_add_left (hd.trans (card_le_univ _)) _

end ZFChain
