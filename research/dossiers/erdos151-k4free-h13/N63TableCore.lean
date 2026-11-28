import N63PriceShapes

namespace Erdos151N63
inductive Decision where
  | pivot (x y : Nat) (center : List Nat)
  | exception83 (perm : Array Nat)
  | exception88 (perm : Array Nat)
  deriving DecidableEq

structure Entry where
  rows : Array Nat
  decision : Decision
  deriving DecidableEq

def mapFin (perm : Array Nat) {n : Nat} [NeZero n] (i : Fin n) : Fin n :=
  ⟨mask perm i.val % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

def Entry.Check (n : Nat) [NeZero n] (e : Entry) : Prop :=
  match e.decision with
  | .pivot x y S =>
    pivotOK e.rows n x y S ∧ priceOK n (deg e.rows n x) (deg e.rows n y) S.length
  | .exception83 p => relabelOK e.rows chart83 n (mapFin p)
  | .exception88 p => relabelOK e.rows chart88 n (mapFin p)

instance (r : Array Nat) (n x y : Nat) (S : List Nat) : Decidable (pivotOK r n x y S) := by
  unfold pivotOK
  infer_instance

instance (r t : Array Nat) (n : Nat) (p : Fin n → Fin n) : Decidable (relabelOK r t n p) := by
  unfold relabelOK Function.Injective
  infer_instance

instance (n a b s : Nat) : Decidable (priceOK n a b s) := by
  unfold priceOK
  infer_instance

instance (n : Nat) [NeZero n] (e : Entry) : Decidable (e.Check n) := by
  unfold Entry.Check
  split <;> infer_instance


def Entry.Fast (e : Entry) : Prop :=
  match e.decision with
  | .pivot x y S =>
    pivotOK e.rows 9 x y S ∧ (deg e.rows 9 x,deg e.rows 9 y,S.length) ∈ nineShapes
  | .exception83 p => relabelOK e.rows chart83 9 (mapFin p)
  | .exception88 p => relabelOK e.rows chart88 9 (mapFin p)

instance (e : Entry) : Decidable e.Fast := by
  unfold Entry.Fast
  split <;> infer_instance

theorem Entry.check_of_fast (e : Entry) (h : e.Fast) : e.Check 9 := by
  rcases e with ⟨r,d⟩
  cases d
  · exact ⟨h.1,nineShapes_sound _ _ _ h.2⟩
  · exact h
  · exact h

end Erdos151N63
