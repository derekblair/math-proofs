import PairQuotient
import Stabilize
import ShiftReach
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
namespace IU.Slack
open Finset
open scoped BigOperators

def objective (w : Nat → Nat) (F : Sys) : Nat := ∑ A∈F, w A.card

theorem compress_objective (w : Nat → Nat) (F : Sys) (i j : Nat) (lt : i<j) :
    objective w (compress F i j) = objective w F := by
  classical
  unfold objective compress
  rw [sum_image (action_inj F i j lt.ne)]
  apply sum_congr rfl
  intro A a
  unfold action
  split
  · rename_i h
    have hi : i∉A.erase j := fun q => h.1.1 (mem_of_mem_erase q)
    rcases h.1 with ⟨_,hj⟩
    rw [move,card_insert_of_notMem hi, card_erase_of_mem hj]
    have hpos := card_pos.mpr ⟨j,hj⟩
    congr 1
    omega
  · rfl

theorem stabilize_objective (w : Nat → Nat) (F : Sys) {n t u : Nat} (ok : IsIU F n t u) :
    ∃ G : Sys, objective w G=objective w F ∧ IsIU G n t u ∧ ClosedUnderPrefix G n := by
  classical
  have main (m : Nat) : ∀ F : Sys, mass F=m → IsIU F n t u →
      ∃ G : Sys, objective w G=objective w F ∧ IsIU G n t u ∧ ElementaryClosed G n := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro F mF ok
      by_cases closed : ElementaryClosed F n
      · exact ⟨F,rfl,ok,closed⟩
      unfold ElementaryClosed at closed
      push Not at closed
      obtain ⟨A,a,i,j,lt,jn,iA,jA,M⟩ := closed
      have D : mass (compress F i j)<m := mF ▸ compress_mass lt a ⟨⟨iA,jA⟩,M⟩
      obtain ⟨G,g1,g2,g3⟩ := ih _ D _ rfl (compress_valid F ok lt jn)
      exact ⟨G,g1.trans (compress_objective w F i j lt),g2,g3⟩
  obtain ⟨G,g1,g2,g3⟩ := main _ F rfl ok
  exact ⟨G,g1,g2,prefix_closed_of_elementary G g2.1 g3⟩

def profile (t s : Nat) (A : Bag) : Nat × Finset Nat × Nat :=
  (pr A t,band A t s,A.card)

theorem band_nested (A : Bag) {t s i : Nat} (hi : i≤s) :
    band A t i = (band A t s).filter (· < t+i) := by
  ext x
  simp only [band,mem_filter]
  constructor <;> intro h
  · exact ⟨⟨h.1,h.2.1,by omega⟩,h.2.2⟩
  · exact ⟨h.1.1,h.1.2.1,h.2⟩

theorem same_profile {A A' B B' : Bag} {t s : Nat}
    (a : profile t s A=profile t s A') (b : profile t s B=profile t s B') :
    Compatible A B t s ↔ Compatible A' B' t s := by
  have ar := congrArg Prod.fst a
  have br := congrArg Prod.fst b
  have ax := congrArg (fun z => z.2.1) a
  have bx := congrArg (fun z => z.2.1) b
  have ac := congrArg (fun z => z.2.2) a
  have bc := congrArg (fun z => z.2.2) b
  change pr A t=pr A' t at ar
  change pr B t=pr B' t at br
  change band A t s=band A' t s at ax
  change band B t s=band B' t s at bx
  change A.card=A'.card at ac
  change B.card=B'.card at bc
  constructor <;> rintro ⟨i,hi,H⟩ <;> refine ⟨i,hi,?_⟩
  · rw [band_nested _ hi,band_nested _ hi,←ax,←bx,←band_nested _ hi,←band_nested _ hi,←ar,←br,←ac,←bc]
    exact H
  · rw [band_nested _ hi,band_nested _ hi,ax,bx,←band_nested _ hi,←band_nested _ hi,ar,br,ac,bc]
    exact H

noncomputable def saturate (F : Sys) (n t s : Nat) : Sys := by
  classical
  exact (range n).powerset.filter fun A => ∃ B∈F, profile t s A=profile t s B

/-- For every nonnegative integral rank-weighted family there is a family
of no smaller score consisting of whole profile fibers. -/
theorem exact_saturation (w : Nat → Nat) (F : Sys) {t u s : Nat}
    (ht : 0<t) (hF : IsIU F (t+u+s) t u) :
    ∃ G : Sys, IsIU G (t+u+s) t u ∧ objective w F≤objective w G ∧
      ∀ A B : Bag, A∈G → B⊆range (t+u+s) →
        profile t s A=profile t s B → B∈G := by
  classical
  obtain ⟨H,h1,h2,h3⟩ := stabilize_objective w F hF
  let G := saturate H (t+u+s) t s
  have M {A : Bag} : A∈G ↔ A⊆range (t+u+s) ∧
      ∃ B∈H, profile t s A=profile t s B := by simp [G,saturate]
  have HG : H⊆G := fun a ha => M.mpr ⟨h2.1 a ha,a,ha,rfl⟩
  refine ⟨G,⟨fun A a => (M.mp a).1,?_⟩,?_,?_⟩
  · intro A a B b
    obtain ⟨_,A',a',ae⟩ := M.mp a
    obtain ⟨_,B',b',be⟩ := M.mp b
    have ax : A.card=A'.card := congrArg (fun z => z.2.2) ae
    have bx : B.card=B'.card := congrArg (fun z => z.2.2) be
    have tA : t≤A.card := by rw [ax]; simpa using (h2.2 A' a' A' a').1
    have tB : t≤B.card := by rw [bx]; simpa using (h2.2 B' b' B' b').1
    have W := shifted_witness_band ht h2 h3 a' b'
    have C := (compatible_iff_witness (ax ▸ tA) (bx ▸ tB)).mpr W
    have D := compatible_sound tA tB ((same_profile ae be).mpr C)
    exact ⟨D.1,by omega⟩
  · rw [←h1]
    apply sum_le_sum_of_subset HG
  · intro A B a b e
    obtain ⟨_,C,c,eq⟩ := M.mp a
    exact M.mpr ⟨b,C,c,e.symm.trans eq⟩

#print axioms exact_saturation
end IU.Slack
