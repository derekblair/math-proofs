import CutOrder

namespace KCut
open CutLift AffineAddress

abbrev Chain (w : List ℤ) (n : ℕ) := Fin (n+1) → Cut w
abbrev Offset {w : List ℤ} {n : ℕ} (f : ℤ → List ℤ) (T : Chain w n) :=
  (i : Fin (n+1)) → Cut (f (T i).letter)

variable {w : List ℤ} {n : ℕ}

def desc (f : ℤ → List ℤ) (T : Chain w n) (D : Offset f T) :
    Chain (w.flatMap f) n :=
  fun i => lift f (T i) (D i)

def ordered (T : Chain w n) : Prop :=
  ∀ j : Fin n, idx (T j.castSucc) ≤ idx (T j.succ)

def strict (T : Chain w n) : Prop :=
  ∀ j : Fin n, idx (T j.castSucc) < idx (T j.succ)

structure Shape (n : ℕ) where
  letters : Fin (n+1) → ℤ
  steps : Fin n → Bool
  deriving DecidableEq

def shape (T : Chain w n) : Shape n :=
  ⟨fun i => (T i).letter, fun j => decide (idx (T j.castSucc) < idx (T j.succ))⟩

def guard (f : ℤ → List ℤ) (S : Shape n) (D : (i : Fin (n+1)) → Cut (f (S.letters i))) :
    Prop :=
  ∀ j : Fin n, S.steps j = true ∨ idx (D j.castSucc) ≤ idx (D j.succ)

def update (f : ℤ → List ℤ) (S : Shape n) (D : (i : Fin (n+1)) → Cut (f (S.letters i))) :
    Shape n :=
  ⟨fun i => (D i).letter, fun j => S.steps j || decide (idx (D j.castSucc) < idx (D j.succ))⟩

theorem shape_step (f : ℤ → List ℤ) (T : Chain w n) (D : Offset f T) (h : ordered T) :
    (ordered (desc f T D) ↔ guard f (shape T) D) ∧
    shape (desc f T D) = update f (shape T) D := by
  constructor
  · simp only [desc, ordered, guard, shape, decide_eq_true_eq,
      fun j : Fin n => (CutOrder.exact_step f (T j.castSucc) (T j.succ)
        (D j.castSucc) (D j.succ) (h j)).1]
  · suffices e : (fun j : Fin n => decide (idx (desc f T D j.castSucc) < idx (desc f T D j.succ))) =
        (fun j : Fin n => (shape T).steps j || decide (idx (D j.castSucc) < idx (D j.succ))) by
      change Shape.mk (fun i => (D i).letter) _ = Shape.mk (fun i => (D i).letter) _
      exact congrArg (Shape.mk (fun i => (D i).letter)) e
    funext j
    apply CutOrder.congrBool
    simp only [shape, Bool.or_eq_true, decide_eq_true_eq]
    change idx (lift f (T j.castSucc) (D j.castSucc)) < idx (lift f (T j.succ) (D j.succ)) ↔ _
    exact (CutOrder.exact_step f (T j.castSucc) (T j.succ) (D j.castSucc) (D j.succ) (h j)).2

theorem parent_ordered (f : ℤ → List ℤ) (T : Chain w n) (D : Offset f T)
    (h : ordered (desc f T D)) : ordered T :=
  fun j => CutOrder.ordered_parent f (T j.castSucc) (T j.succ) (D j.castSucc) (D j.succ) (h j)

theorem unlift_all (f : ℤ → List ℤ) (U : Chain (w.flatMap f) n) :
    ∃ (T : Chain w n) (D : Offset f T), desc f T D = U := by
  classical
  choose T D h using fun i => CutLift.unlift f (U i)
  exact ⟨T,D,funext h⟩

def block (T : Chain w n) (i : Fin n) : ℤ × ℤ :=
  σ (T i.succ).head - σ (T i.castSucc).head

def offsetBlock (P : Fin (n+1) → List ℤ) (i : Fin n) : ℤ × ℤ :=
  σ (P i.succ) - σ (P i.castSucc)

theorem block_desc (f : ℤ → List ℤ) (A : (ℤ×ℤ) →+ (ℤ×ℤ))
    (aff : ∀ x, σ (f x)=A (σ [x])) (T : Chain w n) (D : Offset f T) (i : Fin n) :
    block (desc f T D) i = A (block T i) + offsetBlock (fun i => (D i).head) i := by
  simp only [block,offsetBlock,desc,lift,sig_append,sig_exp f A aff,map_sub]
  abel

def gaps {k : ℕ} (T : Chain w (k+1)) (j : Fin k) : ℤ × ℤ :=
  block T j.succ - block T j.castSucc

def offsets {k : ℕ} (P : Fin ((k+1)+1) → List ℤ) (j : Fin k) : ℤ × ℤ :=
  offsetBlock P j.succ - offsetBlock P j.castSucc

theorem gaps_desc {k : ℕ} (f : ℤ → List ℤ) (A : (ℤ×ℤ) →+ (ℤ×ℤ))
    (aff : ∀ x, σ (f x)=A (σ [x])) (T : Chain w (k+1)) (D : Offset f T) (j : Fin k) :
    gaps (desc f T D) j = A (gaps T j) + offsets (fun i => (D i).head) j := by
  simp only [gaps, offsets, block_desc f A aff, map_sub]
  abel

theorem block_real (T : Chain w n) (j : Fin n) (h : ordered T) :
    ∃ B : List ℤ, (T j.succ).head = (T j.castSucc).head ++ B ∧ block T j = σ B := by
  have sub : (T j.castSucc).head <+: (T j.succ).head := by
    rw [← pre_eq, ← pre_eq (T j.succ)]
    exact List.take_prefix_take_left (h j)
  obtain ⟨B,e⟩ := sub
  refine ⟨B,e.symm,?_⟩
  simp [block, ← e, sig_append]

theorem cut_eq_root (a : ℤ) (U : Cut [a]) : U = TripTrace.rootCut a := by
  apply unique_pos
  change U.head.length = 0
  have h := congrArg List.length U.decomp
  simp only [List.length_cons,List.length_nil,List.length_append] at h
  omega

def root (a : ℤ) : Chain [a] n := fun _ => TripTrace.rootCut a

inductive FromRoot (f : ℤ → List ℤ) (a : ℤ) (n : ℕ) :
    (d : ℕ) → Chain (TripTrace.iter f a d) n → Prop
  | base : FromRoot f a n 0 (root a)
  | grow {d} (T : Chain (TripTrace.iter f a d) n) (D : Offset f T) :
      FromRoot f a n d T → FromRoot f a n (d+1) (desc f T D)

theorem every_representable (f : ℤ → List ℤ) (a : ℤ) (n d : ℕ)
    (U : Chain (TripTrace.iter f a d) n) : FromRoot f a n d U := by
  induction d with
  | zero =>
    have eq : U = root a := funext (fun i => cut_eq_root a (U i))
    rw [eq]
    exact .base
  | succ d ih =>
    obtain ⟨T,D,h⟩ := unlift_all f U
    rw [← h]
    exact .grow T D (ih T)

end KCut

#print axioms KCut.shape_step
#print axioms KCut.every_representable
#print axioms KCut.gaps_desc
#print axioms KCut.block_real
