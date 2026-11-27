import CriticalKernel
import Mathlib.Data.Finset.Card

namespace FolkmanB4
open Finset

variable {E : Type*} [DecidableEq E]

def Splits (T : Finset (Finset E)) (c : E → Bool) : Prop :=
  ∀ t∈T, (∃ e∈t,c e=true) ∧ (∃ e∈t,c e=false)

def Splittable (T : Finset (Finset E)) : Prop := ∃ c, Splits T c

theorem minimal_family {T : Finset (Finset E)} (h : ¬Splittable T) :
    ∃ S ⊆ T, ¬Splittable S ∧ ∀ U, U ⊂ S → Splittable U := by
  classical
  let P (n : Nat) := ∃ S ⊆ T, S.card=n ∧ ¬Splittable S
  have hex : ∃ n, P n := ⟨T.card,T,subset_refl _,rfl,h⟩
  obtain ⟨S,ST,sc,hs⟩ := Nat.find_spec hex
  refine ⟨S,ST,hs,fun U us => ?_⟩
  by_contra hu
  have lt : U.card < Nat.find hex := sc ▸ card_lt_card us
  exact Nat.find_min hex lt ⟨U,us.le.trans ST,rfl,hu⟩

end FolkmanB4
