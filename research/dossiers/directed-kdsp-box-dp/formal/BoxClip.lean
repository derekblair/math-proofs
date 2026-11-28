import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

namespace DirectedBoxDSP

variable {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def admissible (a b cap : F → K) (faces : Finset F) (t : K) : Prop :=
  0 ≤ t ∧ t ≤ 1 ∧
  ∀ f ∈ faces, a f + t * (b f - a f) ≤ cap f

def emptyOrInterval (P : K → Prop) : Prop :=
  (∀ t, ¬ P t) ∨
    ∃ l h, 0 ≤ l ∧ l ≤ h ∧ h ≤ 1 ∧ ∀ t, P t ↔ l ≤ t ∧ t ≤ h

/-- The parameter set of a segment clipped to finitely many signed
coordinate halfspaces is empty or a closed subinterval of the original
unit parameter interval. This includes point intersections and segments
whose original endpoints are both outside. -/
theorem clip_empty_or_interval (a b cap : F → K) (faces : Finset F) :
    emptyOrInterval (admissible a b cap faces) := by
  classical
  induction faces using Finset.induction_on with
  | empty =>
    exact Or.inr ⟨0,1,le_rfl,zero_le_one,le_rfl,by simp [admissible]⟩
  | @insert f faces hf ih =>
    have ext (t : K) : admissible a b cap (insert f faces) t ↔
        admissible a b cap faces t ∧ a f + t * (b f - a f) ≤ cap f := by
      simp [admissible]
      constructor <;> tauto
    rcases ih with H | ⟨l,h,l0,lh,h1,H⟩
    · exact Or.inl fun t ht => H t ((ext t).mp ht).1
    have go (l' h' : K) (ll : 0 ≤ l') (hh : h' ≤ 1)
        (eqv : ∀ t, admissible a b cap (insert f faces) t ↔ l' ≤ t ∧ t ≤ h') :
        emptyOrInterval (admissible a b cap (insert f faces)) := by
      by_cases hor : l' ≤ h'
      · exact Or.inr ⟨l',h',ll,hor,hh,eqv⟩
      · exact Or.inl fun t ht => hor (((eqv t).mp ht).1.trans ((eqv t).mp ht).2)
    by_cases hp : 0 < b f - a f
    · let q := (cap f - a f) / (b f - a f)
      apply go l (min h q) l0 ((min_le_left _ _).trans h1)
      intro t
      rw [ext, H, le_min_iff]
      have he : a f + t*(b f-a f) ≤ cap f ↔ t ≤ q := by
        rw [le_div_iff₀ hp]
        constructor <;> intro hh <;> linarith
      rw [he]
      tauto
    by_cases hn : 0 < a f - b f
    · let q := (a f - cap f) / (a f - b f)
      apply go (max l q) h (l0.trans (le_max_left _ _)) h1
      intro t
      rw [ext, H, max_le_iff]
      have he : a f + t*(b f-a f) ≤ cap f ↔ q ≤ t := by
        rw [div_le_iff₀ hn]
        constructor <;> intro hh <;> linarith
      rw [he]
      tauto
    have hb : b f - a f = 0 := by
      have h₁ := le_of_not_gt hp
      have h₂ := le_of_not_gt hn
      linarith
    by_cases hc : a f ≤ cap f
    · apply go l h l0 h1
      intro t
      simp [ext, H, hb, hc]
    · exact Or.inl fun t ht => hc (by simpa [hb] using ((ext t).mp ht).2)

#print axioms clip_empty_or_interval
end DirectedBoxDSP
