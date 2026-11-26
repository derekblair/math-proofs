import RibbonD3Balanced
import RibbonD3RotateWalk

namespace RibbonD3WordSelection
open RibbonD3MateData RibbonD3MateUse RibbonD3PortEval RibbonD3SignedEval
open RibbonD3ClosureMembership RibbonD3RotateWalk Ribbon5Bridge RibbonDerived3
variable {G : Type*} [Group G]

abbrev Count := Fin 16

def idx (i : Count) : Fin charts.size :=
  ⟨i.val, i.isLt⟩
def mc (i : Count) : Chart := charts[idx i]

def block (i : Count) (n : Nat) : List P :=
  decode ((mc i).ports.toList.take n)

def uBlock (i : Count) := block i (mc i).rotation
def aTail (i : Count) := (block i 32).drop (mc i).rotation
def wTail (i : Count) := (block i 64).drop (mc i).rotation

def dataValid (i : Count) : Prop :=
  (mc i).startSide = false ∧ (block i 128).length = 128 ∧
  (block i 128) = uBlock i ++ wTail i ++ reverseWord (wTail i ++ uBlock i) ∧
  (block i 64) = uBlock i ++ aTail i ++ reverseWord (aTail i ++ uBlock i) ∧
  (block i 64) = uBlock i ++ wTail i ∧
  (block i 32) = uBlock i ++ aTail i ∧
  (run (1:PUnit.{1}) 1 (false,1) (block i 32)).1 = false ∧
  (run (1:PUnit.{1}) 1 (false,1) (uBlock i)).1 = false ∧
  ((mc i).ports.toList.all (fun d => d < 3)) = true
instance (i : Count) : Decidable (dataValid i) := by unfold dataValid; infer_instance

theorem data_valid (i : Count) : dataValid i := by fin_cases i <;> decide +kernel

def rat (x y : G) (i : Count) : G := eval (letter x y) (letters (mc i) 32)
def bal (x y : G) (i : Count) : G := eval (letter x y) (letters (mc i) (mc i).rotation)
def zed (x y : G) (i : Count) : G := rat x y i * (bal x y i)⁻¹ * (rat x y i)⁻¹ * (bal x y i)

theorem act_first (x y : G) (w : List P) : (run x y (false,1) w).1 =
    (run (1:PUnit.{1}) 1 (false,1) w).1 := by
  let f : G →* PUnit.{1} := 1
  have h := mapped_run f x y (false,1) w
  simpa [f] using congrArg Prod.fst h

theorem block_ok (x y : G) (i : Count) (n : Nat) :
    eval (letter x y) (letters (mc i) n) = (run x y (false,1) (block i n)).2 := by
  have V := data_valid i
  rw [letters,V.1]
  apply eval_port_snd
  intro z hz
  apply of_decide_eq_true
  have L : z ∈ (mc i).ports.toList := List.mem_of_mem_take hz
  exact List.all_eq_true.mp V.2.2.2.2.2.2.2.2 z L

theorem runA (x y : G) (i : Count) :
    run x y (start G) (block i 32) = shift (rat x y i) (start G) := by
  have V := data_valid i
  apply Prod.ext
  · change (run x y (false,1) (block i 32)).1 = false
    exact (act_first x y _).trans V.2.2.2.2.2.2.1
  · simpa [start,shift,rat] using (block_ok x y i 32).symm

theorem runU (x y : G) (i : Count) :
    run x y (start G) (uBlock i) = shift (bal x y i) (start G) := by
  have V := data_valid i
  apply Prod.ext
  · change (run x y (false,1) (uBlock i)).1 = false
    exact (act_first x y _).trans V.2.2.2.2.2.2.2.1
  · simpa [start,shift,bal,uBlock] using (block_ok x y i (mc i).rotation).symm

theorem runW (x y : G) (i : Count) :
    run x y (start G) (block i 64) = shift (zed x y i) (start G) := by
  have V := data_valid i
  have A := runA x y i
  rw [V.2.2.2.2.2.1] at A
  have h := rotation_eval x y false _ _ _ _ (runU x y i) A
  rw [←V.2.2.2.1] at h
  exact h

theorem runClosed (d3 : DLS G 3 = ⊥) (x y : G) (i : Count) :
    run x y (start G) (block i 128) = start G := by
  have V := data_valid i
  have A := runW x y i
  rw [V.2.2.2.2.1] at A
  have h := rotation_eval x y false _ _ _ _ (runU x y i) A
  rw [←V.2.2.1] at h
  change run x y (base false) (block i 128) = base false
  have close := RibbonD3Closure.rotateTwice_close d3
    (A_mem_second x y (idx i)) (U_mem_derived x y (idx i)) (U_mem_derived x y (idx i))
  change zed x y i * (bal x y i)⁻¹ * (zed x y i)⁻¹ * bal x y i = 1 at close
  rw [h,close]
  simp [shift]

#print axioms runW
#print axioms runClosed
end RibbonD3WordSelection
