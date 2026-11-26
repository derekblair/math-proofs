import KFactors
import FiniteTripTrace

namespace KFinite
open KCut CutLift AffineAddress
open FiniteTrip (Alpha idxFin byIndex byIndex_round letter_mem)

abbrev State (D : Finset ℤ) (n : ℕ) := (Fin (n+1) → Alpha D) × (Fin n → Bool)

def erase {D : Finset ℤ} {n : ℕ} (S : State D n) : Shape n :=
  ⟨fun i => (S.1 i).val, S.2⟩

theorem erase_inj (D : Finset ℤ) (n : ℕ) : Function.Injective (@erase D n) := by
  intro a b h
  apply Prod.ext
  · funext i
    exact Subtype.ext (congrFun (congrArg Shape.letters h) i)
  · exact congrArg Shape.steps h

def restrictShape (D : Finset ℤ) {w : List ℤ} {n : ℕ} (T : Chain w n)
    (h : ∀ z ∈ w, z ∈ D) : State D n :=
  (fun i => ⟨(T i).letter,h _ (letter_mem (T i))⟩, (shape T).steps)

abbrev Choices {D : Finset ℤ} {n : ℕ} (f : ℤ → List ℤ) (S : State D n) :=
  (i : Fin (n+1)) → Fin (f (S.1 i).val).length

def cuts {D : Finset ℤ} {n : ℕ} {f : ℤ → List ℤ} {S : State D n} (C : Choices f S) :
    (i : Fin (n+1)) → Cut (f ((erase S).letters i)) :=
  fun i => byIndex _ (C i)

def edgeGuard {D : Finset ℤ} {n : ℕ} (f : ℤ → List ℤ) (S : State D n) (C : Choices f S) :=
  KCut.guard f (erase S) (cuts C)

instance {D : Finset ℤ} {n : ℕ} (f : ℤ → List ℤ) (S : State D n) (C : Choices f S) :
    Decidable (edgeGuard f S C) := by unfold edgeGuard KCut.guard; infer_instance

abbrev Candidate (D : Finset ℤ) (n : ℕ) (f : ℤ → List ℤ) :=
  Sigma (fun S : State D n => Choices f S)

abbrev Edge (D : Finset ℤ) (n : ℕ) (f : ℤ → List ℤ) :=
  {c : Candidate D n f // edgeGuard f c.1 c.2}

instance (D : Finset ℤ) (n : ℕ) (f : ℤ → List ℤ) : DecidableEq (Edge D n f) := by
  letI : DecidableEq (Candidate D n f) := @Sigma.instDecidableEqSigma (State D n)
    (fun S => Choices f S) inferInstance (fun _ => inferInstance)
  intro a b
  exact decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

example (D : Finset ℤ) (n : ℕ) : Fintype (State D n) := inferInstance
example (D : Finset ℤ) (n : ℕ) (f : ℤ → List ℤ) : Fintype (Edge D n f) := inferInstance

variable {D : Finset ℤ} {n : ℕ} {f : ℤ → List ℤ}

def src (e : Edge D n f) : State D n := e.val.1

def dst (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D) (e : Edge D n f) : State D n :=
  let F := update f (erase (src e)) (cuts e.val.2)
  (fun i => ⟨F.letters i,closed _ ((src e).1 i).property _ (letter_mem (cuts e.val.2 i))⟩, F.steps)

def stamp {k : ℕ} (e : Edge D (k+1) f) : Fin k → ℤ × ℤ :=
  offsets (fun i => (cuts e.val.2 i).head)

theorem childMem (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
    {w : List ℤ} (h : ∀ z ∈ w, z ∈ D) : ∀ z ∈ w.flatMap f, z ∈ D :=
  FiniteTripStep.child_mem D f closed h

theorem step_matches (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
    {w : List ℤ} {k : ℕ} (T : Chain w (k+1)) (h : ∀ z ∈ w, z ∈ D) (o : ordered T)
    (e : Edge D (k+1) f) (he : src e = restrictShape D T h) :
    ∃ P : Offset f T, ordered (desc f T P) ∧
      dst closed e = restrictShape D (desc f T P) (childMem closed h) ∧
      stamp e = offsets (fun i => (P i).head) := by
  rcases e with ⟨⟨S,C⟩,hc⟩
  change S = restrictShape D T h at he
  subst S
  let P : Offset f T := cuts C
  have hs := shape_step f T P o
  refine ⟨P, hs.1.mpr hc, ?_,rfl⟩
  apply erase_inj
  change update f (shape T) P = shape (desc f T P)
  exact hs.2.symm

theorem step_exists (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
    {w : List ℤ} {k : ℕ} (T : Chain w (k+1)) (h : ∀ z ∈ w, z ∈ D) (o : ordered T)
    (P : Offset f T) (op : ordered (desc f T P)) :
    ∃ e : Edge D (k+1) f, src e = restrictShape D T h ∧
      dst closed e = restrictShape D (desc f T P) (childMem closed h) ∧
      stamp e = offsets (fun i => (P i).head) := by
  let C : Choices f (restrictShape D T h) := fun i => idxFin (P i)
  have pc : (cuts C : Offset f T) = P := funext (fun i => byIndex_round (P i))
  have hg : edgeGuard f (restrictShape D T h) C := by
    change KCut.guard f (shape T) (cuts C) 
    rw [pc]
    exact (shape_step f T P o).1.mp op
  let e : Edge D (k+1) f := ⟨⟨restrictShape D T h,C⟩,hg⟩
  refine ⟨e,rfl,?_,?_⟩
  · apply erase_inj
    change update f (shape T) (cuts C) = shape (desc f T P)
    rw [pc,(shape_step f T P o).2]
  · change offsets (fun i => (cuts C i).head) = _
    rw [pc]

end KFinite

#print axioms KFinite.step_matches
#print axioms KFinite.step_exists
