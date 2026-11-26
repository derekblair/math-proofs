import RibbonAffineUniversalData
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace RibbonAffine.Universal

set_option maxRecDepth 30000
set_option maxHeartbeats 0

def trDelta (B : Branch) (i j : Fin 32) : List Mono :=
  subUV B.u B.v ((position B.word i.val).tr ++ negative (position B.word j.val).tr)

def expDelta (B : Branch) (i j : Fin 32) : ℤ :=
  ((position B.word i.val).i - (position B.word j.val).i) * B.v -
    ((position B.word i.val).j - (position B.word j.val).j) * B.u

def mulDelta (n : ℕ) : List Mono := [(n,0,1),(0,0,-1)]

def combination (B : Branch) (C : Cert) (i j : Fin 32) : List Mono :=
  mulP C.fc B.f ++ mulP C.dc (trDelta B i j) ++ mulP C.mc (mulDelta C.d)

def valid (q : Fin 14) (i j : Fin 32) : Prop :=
  let B := branch q
  let C := cert q i j
  (position B.word i.val).side ≠ (position B.word j.val).side ∨
    (expDelta B i j).natAbs = 2^C.power * C.d ∧
    C.k ∣ B.constant ∧ nf (combination B C i j) = nf [(0,0,C.k)]

instance (q : Fin 14) (i j : Fin 32) : Decidable (valid q i j) := by
  unfold valid
  infer_instance

theorem table_valid (q : Fin 14) (i j : Fin 32) (lt : i.val < j.val) : valid q i j := by
  revert i j lt
  fin_cases q <;> decide +kernel

end RibbonAffine.Universal
