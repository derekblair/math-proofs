import TripTrace

namespace CutOrder
open CutLift TripTrace
variable {w : List ℤ}

theorem exact_step (f : ℤ → List ℤ) (X Y : Cut w) (x : Cut (f X.letter))
    (y : Cut (f Y.letter)) (h : idx X ≤ idx Y) :
    (idx (lift f X x) ≤ idx (lift f Y y) ↔ idx X < idx Y ∨ idx x ≤ idx y) ∧
    (idx (lift f X x) < idx (lift f Y y) ↔ idx X < idx Y ∨ idx x < idx y) := by
  rcases h.lt_or_eq with h | h
  · have z := lift_strict f X Y h x y
    simp [h,z,z.le]
  · have e := unique_pos X Y h
    subst Y
    simp [lift_idx]

theorem ordered_parent (f : ℤ → List ℤ) (X Y : Cut w) (x : Cut (f X.letter))
    (y : Cut (f Y.letter)) (h : idx (lift f X x) ≤ idx (lift f Y y)) :
    idx X ≤ idx Y := by
  by_contra hn
  have z := lift_strict f Y X (by omega) y x
  omega

structure Shape where
  a : ℤ
  b : ℤ
  c : ℤ
  ab : Bool
  bc : Bool
  deriving DecidableEq

def shape (T : Triple w) : Shape :=
  ⟨T.a.letter,T.b.letter,T.c.letter,decide (idx T.a < idx T.b),decide (idx T.b < idx T.c)⟩

def ordered (T : Triple w) : Prop :=
  idx T.a ≤ idx T.b ∧ idx T.b ≤ idx T.c

def guard (f : ℤ → List ℤ) (S : Shape) (a : Cut (f S.a)) (b : Cut (f S.b))
    (c : Cut (f S.c)) : Prop :=
  (S.ab=true ∨ idx a ≤ idx b) ∧ (S.bc=true ∨ idx b ≤ idx c)

def update (f : ℤ → List ℤ) (S : Shape) (a : Cut (f S.a)) (b : Cut (f S.b))
    (c : Cut (f S.c)) : Shape :=
  ⟨a.letter,b.letter,c.letter,S.ab || decide (idx a < idx b),S.bc || decide (idx b < idx c)⟩

theorem congrBool (a b : Bool) (h : (a = true ↔ b = true)) : a=b := by
  cases a <;> cases b <;> simp_all

theorem shape_step (f : ℤ → List ℤ) (T : Triple w) (D : Offset f T) (h : ordered T) :
    (ordered (desc f T D) ↔ guard f (shape T) D.a D.b D.c) ∧
    shape (desc f T D) = update f (shape T) D.a D.b D.c := by
  have x := exact_step f T.a T.b D.a D.b h.1
  have y := exact_step f T.b T.c D.b D.c h.2
  constructor
  · simp only [desc,ordered,guard,shape,decide_eq_true_eq,x.1,y.1]
  · have t (M N : Cut w) (i : Cut (f M.letter)) (j : Cut (f N.letter)) (h : idx M ≤ idx N) :
          decide (idx (lift f M i) < idx (lift f N j)) =
            (decide (idx M < idx N) || decide (idx i < idx j)) := by
      apply congrBool
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using (exact_step f M N i j h).2
    unfold shape update desc
    rw [t _ _ _ _ h.1,t _ _ _ _ h.2] <;> rfl

theorem parent_ordered (f : ℤ → List ℤ) (T : Triple w) (D : Offset f T)
    (h : ordered (desc f T D)) : ordered T :=
  ⟨ordered_parent f T.a T.b D.a D.b h.1,ordered_parent f T.b T.c D.b D.c h.2⟩

end CutOrder

#print axioms CutOrder.shape_step
#print axioms CutOrder.parent_ordered
