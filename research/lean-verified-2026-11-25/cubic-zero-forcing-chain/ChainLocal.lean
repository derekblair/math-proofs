import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace ZFChain
open Finset

def localEdge (mid : Bool) (a b : Fin 8) : Bool :=
  let x := a.val
  let y := b.val
  let ab := fun (i j : ℕ) =>
    (i < 3 && 3 ≤ j && j < 6 && !(i == 0 && j == 3) &&
      !(mid && i == 1 && j == 4)) ||
    (j == 6 && (i == 0 || i == 3)) ||
    (mid && j == 7 && (i == 1 || i == 4))
  ab x y || ab y x

def legal (mid : Bool) (a : Fin 8) : Prop := mid = true ∨ a.val < 7
instance (m) (a) : Decidable (legal m a) := by unfold legal; infer_instance

def locNbr (m : Bool) (a : Fin 8) : Finset (Fin 8) :=
  univ.filter fun b => localEdge m a b

theorem localEdge_symm (m a b) : localEdge m a b = localEdge m b a := by
  cases m <;> fin_cases a <;> fin_cases b <;> decide

theorem localEdge_diag (m a) : localEdge m a a = false := by
  cases m <;> fin_cases a <;> decide

def locFort (m : Bool) (F : Finset (Fin 8)) : Prop :=
  F.Nonempty ∧ (∀ a ∈ F, legal m a) ∧
    ∀ a : Fin 8, a ∉ F → ((locNbr m a) ∩ F).card ≠ 1
instance (m) (F) : Decidable (locFort m F) := by unfold locFort; infer_instance

def forts1 : List (Finset (Fin 8)) :=
  [{1,2},{0,1,3,4},{0,2,3,4},{0,1,3,5},{0,2,3,5},{4,5},{0,1,6},{0,2,6},{3,4,6},{3,5,6}]
def forts2 : List (Finset (Fin 8)) :=
  [{0,1,3,4},{0,2,3,5},{1,2,4,5},{0,2,6},{1,2,4,6},{3,5,6},{1,4,5,6},
   {1,2,7},{0,2,3,7},{0,3,5,7},{4,5,7},{0,1,6,7},{3,4,6,7},{2,5,6,7}]
def localForts (m : Bool) := if m then forts2.toFinset else forts1.toFinset
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem local_Forts_correct (m : Bool) : ∀ F ∈ localForts m, locFort m F := by
  cases m <;> decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem local_Forts_hit (m : Bool) :
    ∀ S : Finset (Fin 8), S.card < 4 → ∃ F ∈ localForts m, Disjoint F S := by
  cases m <;> decide

def localDominates (m : Bool) (D : Finset (Fin 8)) (a : Fin 8) : Prop :=
  a ∈ D ∨ (locNbr m a ∩ D).Nonempty
instance (m) (D) (a) : Decidable (localDominates m D a) := by
  unfold localDominates
  infer_instance

def domCore (m : Bool) (D : Finset (Fin 8)) : Prop :=
  ∀ a : Fin 8, a.val < 6 → localDominates m D a
instance (m) (D) : Decidable (domCore m D) := by unfold domCore; infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem domCore_two (m : Bool) : ∀ D : Finset (Fin 8), domCore m D → 2 ≤ D.card := by
  cases m <;> decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem domCore_port_cost (m : Bool) :
    ∀ D : Finset (Fin 8), domCore m D → D.card = 2 → 6 ∉ D ∧ 7 ∉ D := by
  cases m <;> decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem domCore_middle_demand :
    ∀ D : Finset (Fin 8), domCore true D → D.card = 2 →
      ¬ localDominates true D 6 ∨ ¬ localDominates true D 7 := by
  decide

theorem locNbr_classes (m : Bool) (a : Fin 8) (ha : legal m a) :
    (locNbr m a).card = if a.val < 6 then 3 else 2 := by
  cases m <;> fin_cases a <;> revert ha <;> decide

theorem locEdge_legal (m a b) :
    localEdge m a b = true → legal m a ∧ legal m b := by
  cases m <;> fin_cases a <;> fin_cases b <;> decide

theorem loc_no_triangle (m a b c) :
    localEdge m a b = true → localEdge m b c = true → localEdge m c a = false := by
  cases m <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

end ZFChain
