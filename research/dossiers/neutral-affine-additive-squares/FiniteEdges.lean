import EdgeExpansion
import Mathlib.Data.List.Infix

namespace FiniteEdges
open WeightedWalk EdgeExpansion
variable {V I : Type*}
variable (src dst : I → V) (weight : I → ℤ)

def valid : Node V I → Prop
  | .inl _ => True
  | .inr (i,R) => R ∈ (UnitCodes.code (weight i)).tails

abbrev S := { x : Node V I // valid weight x }

def liftBase (v : V) : S (V:=V) weight := ⟨base v, trivial⟩

theorem next_valid {x y : Node V I} {k : ℤ}
    (a : arc src dst weight x k y) (h : valid weight x) : valid weight y := by
  have tail (i : I) (k : ℤ) (R : List ℤ)
      (g : (k::R) <:+ UnitCodes.code (weight i)) : valid weight (atList dst i R) := by
    have s : R <:+ k::R := ⟨[k],rfl⟩
    have f := s.trans g
    cases R with
    | nil => trivial
    | cons k R => exact (List.mem_tails _ _).mpr f
  cases a with
  | start i e => exact tail i _ _ ⟨[],e.symm⟩
  | rest i k R => exact tail i k R ((List.mem_tails _ _).mp h)

theorem reachable_unit {x y : Node V I} {k : ℤ}
    (a : arc src dst weight x k y) (h : valid weight x) : k=1 ∨ k= -1 := by
  cases a with
  | start i e => exact UnitCodes.unit (weight i) (by rw [e]; simp)
  | rest i k R =>
    obtain ⟨P,hP⟩ := (List.mem_tails _ _).mp h
    exact UnitCodes.unit (weight i) (by rw [← hP]; simp)

def restricted (x : S (V:=V) weight) (k : ℤ) (y : S (V:=V) weight) :=
  arc src dst weight x.val k y.val

theorem restrict_walk {x y : Node V I} {L : List ℤ}
    (w : Walk (arc src dst weight) x y L) (hx : valid weight x) :
    ∃ hy : valid weight y, Walk (restricted src dst weight) ⟨x,hx⟩ ⟨y,hy⟩ L := by
  induction w with
  | nil x => exact ⟨hx,.nil _⟩
  | @step x y z k L a w ih =>
    obtain ⟨hy,p⟩ := ih (next_valid src dst weight a hx)
    exact ⟨hy,.step (show restricted src dst weight ⟨x,hx⟩ k ⟨y,next_valid src dst weight a hx⟩ from a) p⟩

theorem unrestrict_walk {x y : S (V:=V) weight} {L : List ℤ}
    (w : Walk (restricted src dst weight) x y L) :
    Walk (arc src dst weight) x.val y.val L := by
  induction w with
  | nil x => exact .nil _
  | step a w ih => exact .step a ih

variable [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def codes : Finset (Node V I) :=
  (Finset.univ.image Sum.inl) ∪ (Finset.univ.biUnion fun i : I =>
    ((UnitCodes.code (weight i)).tails.toFinset).image fun R => Sum.inr (i,R))

theorem mem_codes (x : Node V I) : x ∈ codes weight ↔ valid weight x := by
  cases x with
  | inl v => simp [codes,valid]
  | inr p => rcases p with ⟨i,R⟩; simp [codes,valid,eq_comm]

instance : Fintype (S (V:=V) weight) :=
  Fintype.ofFinset (codes weight) (mem_codes weight)

def startTest (i : I) (x : V) (k : ℤ) (y : Node V I) : Prop :=
  match UnitCodes.code (weight i) with
  | [] => False
  | e::R => src i=x ∧ e=k ∧ atList dst i R=y

instance (i : I) (x : V) (k : ℤ) (y : Node V I) :
    Decidable (startTest src dst weight i x k y) := by
  unfold startTest
  split <;> infer_instance

def cond (x : Node V I) (k : ℤ) (y : Node V I) : Prop :=
  match x with
  | .inl x => ∃ i, startTest src dst weight i x k y
  | .inr (_,[]) => False
  | .inr (i,e::R) => e=k ∧ atList dst i R=y

instance (x : Node V I) (k : ℤ) (y : Node V I) :
    Decidable (cond src dst weight x k y) := by
  cases x with
  | inl x => unfold cond; infer_instance
  | inr p => rcases p with ⟨i,R⟩; cases R <;> unfold cond <;> infer_instance

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
theorem cond_iff (x : Node V I) (k : ℤ) (y : Node V I) :
    cond src dst weight x k y ↔ arc src dst weight x k y := by
  constructor
  · cases x with
    | inl x =>
      rintro ⟨i,h⟩
      unfold startTest at h
      split at h
      · contradiction
      · rename_i e R eq
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact .start i eq
    | inr p =>
      rcases p with ⟨i,R⟩
      cases R with
      | nil => simp [cond]
      | cons e R =>
        rintro ⟨rfl,rfl⟩
        exact .rest i e R
  · intro a
    cases a with
    | start i h => exact ⟨i, by simp [startTest,h]⟩
    | rest i e R => exact ⟨rfl,rfl⟩

instance (x y : S (V:=V) weight) (k : ℤ) :
    Decidable (restricted src dst weight x k y) :=
  decidable_of_iff _ (cond_iff src dst weight x.val k y.val)

def test (x y : V) : Bool :=
  FiniteBalance.accept (fun a b => restricted src dst weight a 1 b)
    (fun a b => restricted src dst weight a (-1) b) (liftBase weight x) (liftBase weight y)

theorem test_iff (x y : V) :
    test src dst weight x y = true ↔ ∃ L, Walk (edge src dst weight) x y L ∧ L.sum=0 := by
  rw [EdgeExpansion.zero_iff, test, FiniteBalance.acceptance_iff]
  have eq : FiniteBalance.edge (fun a b => restricted src dst weight a 1 b)
      (fun a b => restricted src dst weight a (-1) b) = restricted src dst weight := by
    funext a k b
    apply propext
    constructor
    · rintro (⟨rfl,h⟩ | ⟨rfl,h⟩) <;> exact h
    · intro h
      rcases reachable_unit src dst weight h a.property with rfl | rfl
      · exact Or.inl ⟨rfl,h⟩
      · exact Or.inr ⟨rfl,h⟩
  rw [eq]
  constructor
  · rintro ⟨L,w,h⟩; exact ⟨L,unrestrict_walk src dst weight w,h⟩
  · rintro ⟨L,w,h⟩
    obtain ⟨hy,p⟩ := restrict_walk src dst weight w (by trivial)
    exact ⟨L,p,h⟩

end FiniteEdges

#print axioms FiniteEdges.test_iff
