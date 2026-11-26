import CutOrder
import PhaseFinite

namespace FiniteTrip

open CutLift TripTrace CutOrder AffineAddress
variable {w : List ℤ}

def idxFin (C : Cut w) : Fin w.length :=
  ⟨idx C, by
    have h := congrArg List.length C.decomp
    simp only [List.length_append,List.length_cons,idx] at *
    omega⟩

def byIndex (w : List ℤ) (i : Fin w.length) : Cut w where
  head := w.take i.val
  letter := w[i.val]
  tail := w.drop (i.val+1)
  decomp := by
    have h := List.take_append_drop i.val w
    rw [List.drop_eq_getElem_cons i.isLt] at h
    exact h.symm

theorem byIndex_pos (i : Fin w.length) : idx (byIndex w i) = i.val := by
  simp only [byIndex,idx,List.length_take]
  omega

theorem byIndex_round (C : Cut w) : byIndex w (idxFin C) = C :=
  unique_pos _ _ (byIndex_pos _)

theorem letter_mem (T : Cut w) : T.letter ∈ w := (congrArg (fun l : List ℤ => T.letter ∈ l) T.decomp).mpr (by simp)

abbrev Alpha (D : Finset ℤ) := {z : ℤ // z ∈ D}
abbrev State (D : Finset ℤ) := Alpha D × Alpha D × Alpha D × Bool × Bool

def restrictShape (D : Finset ℤ) (T : Triple w) (h : ∀ z ∈ w, z ∈ D) : State D :=
  (⟨T.a.letter,h _ (letter_mem T.a)⟩, ⟨T.b.letter,h _ (letter_mem T.b)⟩,
   ⟨T.c.letter,h _ (letter_mem T.c)⟩,(shape T).ab,(shape T).bc)

def erase {D : Finset ℤ} (S : State D) : Shape :=
  ⟨S.1.val,S.2.1.val,S.2.2.1.val,S.2.2.2.1,S.2.2.2.2⟩

theorem erase_shape (D : Finset ℤ) (T : Triple w) (h : ∀ z ∈ w, z ∈ D) :
    erase (restrictShape D T h) = shape T := rfl

theorem erase_inj (D : Finset ℤ) : Function.Injective (@erase D) := by
  intro a b h
  apply Prod.ext
  · exact Subtype.ext (congrArg Shape.a h)
  apply Prod.ext
  · exact Subtype.ext (congrArg Shape.b h)
  apply Prod.ext
  · exact Subtype.ext (congrArg Shape.c h)
  apply Prod.ext
  · exact congrArg Shape.ab h
  · exact congrArg Shape.bc h

variable (D : Finset ℤ) (f : ℤ → List ℤ)

abbrev Choices (D : Finset ℤ) (f : ℤ → List ℤ) (S : State D) :=
  Fin (f S.1.val).length × Fin (f S.2.1.val).length × Fin (f S.2.2.1.val).length

def cA {D : Finset ℤ} {f : ℤ → List ℤ} {S : State D} (c : Choices D f S) :=
  byIndex (f S.1.val) c.1
def cB {D : Finset ℤ} {f : ℤ → List ℤ} {S : State D} (c : Choices D f S) :=
  byIndex (f S.2.1.val) c.2.1
def cC {D : Finset ℤ} {f : ℤ → List ℤ} {S : State D} (c : Choices D f S) :=
  byIndex (f S.2.2.1.val) c.2.2

def guardState (S : State D) (c : Choices D f S) : Prop :=
  CutOrder.guard f (erase S) (cA c) (cB c) (cC c)

instance (S : State D) (c : Choices D f S) : Decidable (guardState D f S c) := by
  unfold guardState CutOrder.guard
  infer_instance

abbrev Candidate (D : Finset ℤ) (f : ℤ → List ℤ) := Sigma (Choices D f)
abbrev Edge (D : Finset ℤ) (f : ℤ → List ℤ) :=
  {i : Candidate D f // guardState D f i.1 i.2}

def src (i : Edge D f) : State D := i.val.1

def dst (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
    (i : Edge D f) : State D :=
  let S := src D f i
  let a := cA i.val.2
  let b := cB i.val.2
  let c := cC i.val.2
  (⟨a.letter,closed _ S.1.property _ (letter_mem a)⟩,
   ⟨b.letter,closed _ S.2.1.property _ (letter_mem b)⟩,
   ⟨c.letter,closed _ S.2.2.1.property _ (letter_mem c)⟩,
   (update f (erase S) a b c).ab,(update f (erase S) a b c).bc)

def stamp (i : Edge D f) : ℤ × ℤ :=
  σ (cA i.val.2).head + σ (cC i.val.2).head - (σ (cB i.val.2).head + σ (cB i.val.2).head)

instance : Fintype (Alpha D) := D.fintypeCoeSort
instance : DecidableEq (Edge D f) := by
  letI : DecidableEq (Candidate D f) := @Sigma.instDecidableEqSigma (State D) (Choices D f) inferInstance (fun _ => inferInstance)
  intro a b
  exact decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

example : Fintype (State D) := inferInstance
example : Fintype (Edge D f) := inferInstance

end FiniteTrip

#print axioms FiniteTrip.byIndex_round
#print axioms FiniteTrip.erase_inj
