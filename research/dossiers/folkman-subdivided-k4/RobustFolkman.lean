import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RobustFolkman
open Finset
variable {E : Type*} [DecidableEq E]

def Monochrom (c : E → Bool) (T : Finset E) : Prop :=
  ∀ e∈T, ∀ f∈T, c e=c f

noncomputable def mono (T : Finset (Finset E)) (c : E → Bool) : Finset (Finset E) := by
  classical
  exact T.filter (Monochrom c)

def cutEdges (F : Finset (Finset E)) (pick : Finset E → E) : Finset E := F.image pick

def lost (T : Finset (Finset E)) (D : Finset E) : Finset (Finset E) :=
  T.filter fun t => ¬Disjoint D t

def alive (T : Finset (Finset E)) (D : Finset E) : Finset (Finset E) :=
  T.filter fun t => Disjoint D t

def charge (T F : Finset (Finset E)) (pick : Finset E → E) : Nat :=
  ∑ H∈F, (T.filter fun t => pick H∈t).card

theorem loss_le_charge (T F : Finset (Finset E)) (pick : Finset E → E) :
    (lost T (cutEdges F pick)).card≤charge T F pick := by
  classical
  have sat : lost T (cutEdges F pick) ⊆ F.biUnion (fun h => T.filter fun t => pick h∈t) := by
    intro t ht
    have ⟨hT,hD⟩ := mem_filter.mp ht
    rw [Finset.not_disjoint_iff] at hD
    obtain ⟨e,hde,hte⟩ := hD
    obtain ⟨h,hh,rfl⟩ := mem_image.mp hde
    exact mem_biUnion.mpr ⟨h,hh,mem_filter.mpr ⟨hT,hte⟩⟩
  exact (card_le_card sat).trans card_biUnion_le

theorem all_colorings_retain
    (T F : Finset (Finset E)) (pick : Finset E → E)
    (robust : ∀ c : E → Bool, charge T F pick < (mono T c).card) :
    ∀ c : E → Bool, ∃ t ∈ alive T (cutEdges F pick), Monochrom c t := by
  classical
  intro c
  have h := (loss_le_charge T F pick).trans_lt (robust c)
  obtain ⟨t,m,live⟩ := exists_mem_notMem_of_card_lt_card h
  have H : t∈T ∧ Monochrom c t := mem_filter.mp m
  have d : Disjoint (cutEdges F pick) t := by
    by_contra nd
    exact live (mem_filter.mpr ⟨H.1,nd⟩)
  exact ⟨t,mem_filter.mpr ⟨H.1,d⟩,H.2⟩

/-- Every losing triangle is charged to some copy whose chosen edge it uses;
the same deletion destroys every forbidden copy originally present. -/
theorem robust_avoidance (G : Finset E) (T F : Finset (Finset E))
    (pick : Finset E → E) (hit : ∀ H∈F, pick H∈H)
    (robust : ∀ c : E → Bool, charge T F pick < (mono T c).card) :
    let D := cutEdges F pick
    (∀ H∈F, ¬H⊆G\D) ∧ ∀ c : E → Bool, ∃ t∈alive T D, Monochrom c t := by
  intro D
  refine ⟨?_,all_colorings_retain T F pick robust⟩
  intro H h sub
  exact (mem_sdiff.mp (sub (hit H h))).2 (mem_image.mpr ⟨H,h,rfl⟩)

#print axioms robust_avoidance
end RobustFolkman
