import DigitLinear
import FiniteReach

namespace DigitFinite
open DigitLinear
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable (A : J→I→ℤ) (b : J→ℤ)

abbrev Cell (B : ℤ) := {z : ℤ // z∈IntegerTrace.box B}
abbrev State (J : Type*) (B : ℤ) := J → Cell B

instance (B : ℤ) : Fintype (Cell B) := (IntegerTrace.box B).fintypeCoeSort

def erase {B : ℤ} (x : State J B) : J→ℤ := fun j => (x j).val

def init : State J (baseBound A b) :=
  fun j => ⟨b j,(IntegerTrace.box_iff _ _).mpr (base_b A b j)⟩
def goal : State J (baseBound A b) :=
  fun _ => ⟨0,(IntegerTrace.box_iff _ _).mpr (by simpa using base_nonneg A b)⟩

def relation (x y : State J (baseBound A b)) : Prop :=
  DigitLinear.step A (erase x) (erase y)

instance (x y : State J (baseBound A b)) : Decidable (relation A b x y) := by
  unfold relation DigitLinear.step
  infer_instance

theorem path_sound (x : State J (baseBound A b))
    (p : FiniteReach.Path (relation A b) (goal A b) x) : Accept A (erase x) := by
  induction p with
  | done => exact Accept.done
  | more h p ih => exact .more h ih

theorem path_full {v : J→ℤ} (h : Accept A v)
    (bd : ∀ j, |v j| ≤ baseBound A b) :
    FiniteReach.Path (relation A b) (goal A b)
      (fun j => ⟨v j,(IntegerTrace.box_iff _ _).mpr (bd j)⟩) := by
  induction h with
  | done => exact .done
  | @more p q h v ih =>
    obtain ⟨d,he⟩ := h
    have qb (j : J) : |q j| ≤ baseBound A b :=
      carry_stays _ _ _ _ (he j) (bd j) (base_digit A b d j)
    let nxt : State J (baseBound A b) := fun j => ⟨q j,(IntegerTrace.box_iff _ _).mpr (qb j)⟩
    have w : relation A b (fun j => ⟨p j,(IntegerTrace.box_iff _ _).mpr (bd j)⟩) nxt := ⟨d,he⟩
    exact .more w (ih qb)

def decideCoefficients : Bool :=
  FiniteReach.test (relation A b) (goal A b) (init A b)

theorem correct : decideCoefficients A b=true ↔ ∃ x : I→ℕ, eval A x=b := by
  rw [decideCoefficients,FiniteReach.test_iff]
  constructor
  · intro h
    exact sound A b (path_sound A b _ h)
  · intro h
    exact path_full A b (complete A b h) (base_b A b)

end DigitFinite

#print axioms DigitFinite.correct
