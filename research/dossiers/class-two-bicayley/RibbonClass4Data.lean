import HaarClass4Projection

namespace RibbonClass4Data
open HaarClass4Table

inductive Branch | a | b | d
  deriving DecidableEq

def pick : Fin 3 → Branch := ![.a,.b,.d]

def signs (br : Branch) (n : Nat) : Bool :=
  let row : Array Bool := match br with
  | .a => #[false,true,false,false,true,true,true,false,true,true,false,false,false,true,true,false,
            true,false,false,true,false,false,false,true,true,false,true,true,false,false,true,true]
  | .b => #[false,false,false,false,true,true,true,false,false,true,false,true,true,false,true,true,
            false,false,false,true,true,false,true,true,false,true,false,false,true,true,true,false]
  | .d => #[false,false,true,false,false,false,true,true,false,true,true,false,false,true,true,true,
            true,false,false,false,true,true,false,false,true,false,false,true,true,true,false,true]
  row[n]!

def leftX (p : Row) : Row :=
  ⟨p.i-1,p.j,p.c,p.u-p.c,p.v,p.a-p.u,p.b-p.v,p.d⟩
def leftY (p : Row) : Row :=
  ⟨p.i,p.j-1,p.c-p.i,p.u-tri p.i,p.v-(p.c-p.i),
    p.a-tet p.i,p.b-(p.u-tri p.i),p.d-p.v⟩

theorem cancelX (p : Row) : rightX (leftX p)=p := by
  cases p
  simp [rightX,leftX]
theorem cancelY (p : Row) : rightY (leftY p)=p := by
  cases p
  simp [rightY,leftY]

def step (br : Branch) (n : Nat) (p : Row) : Row :=
  if n%2=0 then (if signs br n then rightX p else leftX p)
  else (if signs br n then rightY p else leftY p)

def row (br : Branch) : Nat → Row
  | 0 => base
  | i+1 => step br i (row br i)
def P (b : Branch) (n : Fin 32) := row b n.val

def suitable (i : ℤ) : Prop := i = -2 ∨ i = -1 ∨ i=0 ∨ i=1
instance (i : ℤ) : Decidable (suitable i) := by unfold suitable; infer_instance

def small (i : ℤ) : Prop := i=1 ∨ i= -1 ∨ i=2 ∨ i= -2 ∨ i=3 ∨ i= -3
instance (i : ℤ) : Decidable (small i) := by unfold small; infer_instance

def unit (i : ℤ) : Prop := i=1 ∨ i= -1
instance (i : ℤ) : Decidable (unit i) := by unfold unit; infer_instance

def admissible (b : Branch) (d : Row) : Prop :=
  small d.i ∨ small d.j ∨ (d.i=0 ∧ d.j=0 ∧ small d.c) ∨
    (d.i=0 ∧ d.j=0 ∧ d.c=0 ∧
      (match b with
       | .a => (unit d.u ∧ d.v=0) ∨ (d.u=0 ∧ d.v=0 ∧ unit d.a ∧ d.b=0 ∧ d.d=0)
       | .b => (unit d.u ∧ d.v=0) ∨ (d.u=0 ∧ d.v=0 ∧ d.a=0 ∧ unit d.b ∧ d.d=0)
       | .d => (d.u=0 ∧ unit d.v) ∨ (d.u=0 ∧ d.v=0 ∧ d.a=0 ∧ d.b=0 ∧ unit d.d)))
instance (b : Branch) (d : Row) : Decidable (admissible b d) := by
  unfold admissible
  cases b <;> infer_instance

theorem range : ∀ (b : Fin 3) (i : Fin 32), suitable (P (pick b) i).i := by decide +kernel
theorem closed : ∀ b : Fin 3, row (pick b) 32=base := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sep : ∀ (b : Fin 3) (i j : Fin 32), i≠j → admissible (pick b) (diff (P (pick b) i) (P (pick b) j)) := by
  decide +kernel

end RibbonClass4Data
#print axioms RibbonClass4Data.sep
