import HaarDerivedBarbellData
import Mathlib.Data.List.FinRange

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
namespace HaarDerivedBarbell
open HaarDerivedWreathCore HaarDerivedWreathTrace

instance : DecidableEq Q := fun a b =>
  decidable_of_iff (a.right=b.right ∧ ∀ c : Bool, ∀ j : Fin 13,
    a.left c (j.val : HaarDerivedGirth22.S)=b.left c (j.val : HaarDerivedGirth22.S))
    ⟨fun h => HaarDerivedGirth22.G.ext' (fun c j => by
      simpa only [ZMod.natCast_zmod_val] using h.2 c ⟨j.val,ZMod.val_lt j⟩) h.1,
     fun h => ⟨congrArg HaarDerivedGirth22.G.right h, fun _ _ => by rw [h]⟩⟩

abbrev x : Q := HaarDerivedGirth22.x
abbrev y : Q := HaarDerivedGirth22.y

def row (i : ℕ) := rows[i]?.getD ((false,0,#[]),0,0)

def base (i : ℕ) : Bool × Q := decode (row i).1

def light (i : ℕ) (b : Bool) : ZMod 3 :=
  if b then (row i).2.2 else (row i).2.1

def marker (b : Bool) : Bool × Q := if b then marker1 else marker0

def code (i : ℕ) : Fin 3 := tags[i]?.getD 0

def GoodRow (i : ℕ) : Prop :=
  base (i+1) = step x y (base i) (code i) ∧
    ∀ b : Bool, light (i+1) b = light i b +
      (edgeFlow x y (base i) (code i) (marker b).1 (marker b).2 : ZMod 3)

instance (i : ℕ) : Decidable (GoodRow i) := by dsimp [GoodRow]; infer_instance

def hash (i : Fin 128) : Bool × ℕ × ZMod 3 × ZMod 3 :=
  ((base i).1, HaarDerivedGirth22.key (base i).2, light i false, light i true)

theorem good_nodup : (List.ofFn hash).Nodup := by decide

theorem base0 : base 0 = (false, (1 : Q)) := by decide
theorem base22 : base 22 = (false, (1 : Q)) := by decide
theorem base64 : base 64 = (false, (1 : Q)) := by decide
theorem init_light (b : Bool) : light 0 b = 0 := by decide +revert

-- Individual small bank checks keep kernel reduction predictable.
theorem bank_0 (i : Fin 8) : GoodRow (0 + i.val) := by decide +revert
theorem bank_1 (i : Fin 8) : GoodRow (8 + i.val) := by decide +revert
theorem bank_2 (i : Fin 8) : GoodRow (16 + i.val) := by decide +revert
theorem bank_3 (i : Fin 8) : GoodRow (24 + i.val) := by decide +revert
theorem bank_4 (i : Fin 8) : GoodRow (32 + i.val) := by decide +revert
theorem bank_5 (i : Fin 8) : GoodRow (40 + i.val) := by decide +revert
theorem bank_6 (i : Fin 8) : GoodRow (48 + i.val) := by decide +revert
theorem bank_7 (i : Fin 8) : GoodRow (56 + i.val) := by decide +revert
theorem bank_8 (i : Fin 8) : GoodRow (64 + i.val) := by decide +revert
theorem bank_9 (i : Fin 8) : GoodRow (72 + i.val) := by decide +revert
theorem bank_10 (i : Fin 8) : GoodRow (80 + i.val) := by decide +revert
theorem bank_11 (i : Fin 8) : GoodRow (88 + i.val) := by decide +revert
theorem bank_12 (i : Fin 8) : GoodRow (96 + i.val) := by decide +revert
theorem bank_13 (i : Fin 8) : GoodRow (104 + i.val) := by decide +revert
theorem bank_14 (i : Fin 8) : GoodRow (112 + i.val) := by decide +revert
theorem bank_15 (i : Fin 8) : GoodRow (120 + i.val) := by decide +revert
theorem good_row (i : ℕ) (hi : i < 128) : GoodRow i := by
  let j : Fin 8 := ⟨i%8, Nat.mod_lt _ (by decide)⟩
  by_cases h0 : i < 8
  · convert bank_0 j using 1 <;> dsimp [j] <;> omega
  by_cases h1 : i < 16
  · convert bank_1 j using 1 <;> dsimp [j] <;> omega
  by_cases h2 : i < 24
  · convert bank_2 j using 1 <;> dsimp [j] <;> omega
  by_cases h3 : i < 32
  · convert bank_3 j using 1 <;> dsimp [j] <;> omega
  by_cases h4 : i < 40
  · convert bank_4 j using 1 <;> dsimp [j] <;> omega
  by_cases h5 : i < 48
  · convert bank_5 j using 1 <;> dsimp [j] <;> omega
  by_cases h6 : i < 56
  · convert bank_6 j using 1 <;> dsimp [j] <;> omega
  by_cases h7 : i < 64
  · convert bank_7 j using 1 <;> dsimp [j] <;> omega
  by_cases h8 : i < 72
  · convert bank_8 j using 1 <;> dsimp [j] <;> omega
  by_cases h9 : i < 80
  · convert bank_9 j using 1 <;> dsimp [j] <;> omega
  by_cases h10 : i < 88
  · convert bank_10 j using 1 <;> dsimp [j] <;> omega
  by_cases h11 : i < 96
  · convert bank_11 j using 1 <;> dsimp [j] <;> omega
  by_cases h12 : i < 104
  · convert bank_12 j using 1 <;> dsimp [j] <;> omega
  by_cases h13 : i < 112
  · convert bank_13 j using 1 <;> dsimp [j] <;> omega
  by_cases h14 : i < 120
  · convert bank_14 j using 1 <;> dsimp [j] <;> omega
  convert bank_15 j using 1 <;> dsimp [j] <;> omega

end HaarDerivedBarbell
