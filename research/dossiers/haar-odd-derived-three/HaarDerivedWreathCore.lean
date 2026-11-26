import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import HaarSharpPortGeometry

namespace HaarDerivedWreathCore
open scoped commutatorElement
variable {Q : Type*} [Group Q]
abbrev Lamps (Q : Type*) := Bool → Q → ZMod 3

structure W (Q : Type*) where
  lamp : Lamps Q
  pos : Q

@[ext] theorem W.ext' {a b : W Q} (hl : ∀ b' q, a.lamp b' q = b.lamp b' q)
    (hr : a.pos = b.pos) : a = b := by
  cases a; cases b; congr; funext t j; exact hl t j

def mul (a b : W Q) : W Q :=
  ⟨fun t j => a.lamp t j + b.lamp t (a.pos⁻¹ * j), a.pos * b.pos⟩

def unit : W Q := ⟨fun _ _ => 0,1⟩

def inv (a : W Q) : W Q :=
  ⟨fun t j => -(a.lamp t (a.pos * j)), a.pos⁻¹⟩

instance : Group (W Q) where
  mul := mul
  one := unit
  inv := inv
  mul_assoc := by
    intro a b c
    apply W.ext'
    · intro t j; change (mul (mul a b) c).lamp t j = (mul a (mul b c)).lamp t j
      simp [mul,mul_inv_rev,mul_assoc,add_assoc]
    · change (mul (mul a b) c).pos = (mul a (mul b c)).pos
      simp [mul,mul_assoc]
  one_mul := by
    intro a; apply W.ext'
    · intro t j; change (mul unit a).lamp t j = a.lamp t j; simp [mul,unit]
    · change (mul unit a).pos = a.pos; simp [mul,unit]
  mul_one := by
    intro a; apply W.ext'
    · intro t j; change (mul a unit).lamp t j = a.lamp t j; simp [mul,unit]
    · change (mul a unit).pos = a.pos; simp [mul,unit]
  inv_mul_cancel := by
    intro a; apply W.ext'
    · intro t j; change (mul (inv a) a).lamp t j = unit.lamp t j
      simp [mul,inv,unit]
    · change (mul (inv a) a).pos = unit.pos
      simp [mul,inv,unit]

def π : W Q →* Q where
  toFun := W.pos
  map_one' := rfl
  map_mul' _ _ := rfl

def coords : W Q ≃ (Lamps Q × Q) where
  toFun a := (a.lamp,a.pos)
  invFun p := ⟨p.1,p.2⟩
  left_inv a := by cases a; rfl
  right_inv p := by cases p; rfl

instance [Finite Q] : Finite (W Q) := Finite.of_equiv _ coords.symm

theorem odd_group [Finite Q] (hq : Odd (Nat.card Q)) : Odd (Nat.card (W Q)) := by
  rw [Nat.card_congr coords, Nat.card_prod]
  have c : Nat.card (Lamps Q)=3^(2 * Nat.card Q) := by
    rw [Nat.card_fun,Nat.card_fun,Nat.card_eq_fintype_card (α:=ZMod 3),ZMod.card]
    simp [←pow_mul,Nat.mul_comm]
  rw [c]
  exact (by decide : Odd (3:ℕ)).pow.mul hq

theorem ker_comm (a b : W Q) (ha : a ∈ (π : W Q→*Q).ker)
    (hb : b ∈ (π : W Q→*Q).ker) : a*b=b*a := by
  change a.pos=1 at ha
  change b.pos=1 at hb
  apply W.ext'
  · intro t j; change (mul a b).lamp t j = (mul b a).lamp t j
    simp [mul,ha,hb,add_comm]
  · change (mul a b).pos=(mul b a).pos
    simp [mul,ha,hb]

theorem derived_next (d : ℕ) (h : derivedSeries Q d=⊥) :
    derivedSeries (W Q) (d+1)=⊥ := by
  have dker : derivedSeries (W Q) d ≤ (π : W Q→*Q).ker := by
    intro a ha
    change π a = 1
    have les := map_derivedSeries_le_derivedSeries (π : W Q→*Q) d
    rw [h] at les
    simpa using les (Subgroup.mem_map_of_mem π ha)
  rw [derivedSeries_succ, eq_bot_iff]
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (ker_comm a b (dker ha) (dker hb)))

def atPos [DecidableEq Q] (b : Bool) (r : Q) : Lamps Q :=
  fun c q => if b=c ∧ r=q then 1 else 0

def up [DecidableEq Q] (b : Bool) (x : Q) : W Q := ⟨atPos b 1,x⟩

theorem positive [DecidableEq Q] (b : Bool) (x : Q) (u : W Q) (c : Bool) (j : Q) :
    (u*up b x).lamp c j=u.lamp c j+atPos b u.pos c j := by
  change u.lamp c j+atPos b 1 c (u.pos⁻¹*j)=_
  simp [atPos,eq_comm,inv_mul_eq_iff_eq_mul]

theorem negative [DecidableEq Q] (b : Bool) (x : Q) (u : W Q) (c : Bool) (j : Q) :
    (u*(up b x)⁻¹).lamp c j=u.lamp c j-atPos b (u.pos*x⁻¹) c j := by
  change u.lamp c j+-atPos b 1 c (x*(u.pos⁻¹*j))=_
  rw [sub_eq_add_neg]
  have e : 1=x*(u.pos⁻¹*j) ↔ u.pos*x⁻¹=j := by
    rw [←mul_assoc, show x*u.pos⁻¹=(u.pos*x⁻¹)⁻¹ by simp [mul_inv_rev]]
    exact eq_comm.trans inv_mul_eq_one
  simp only [atPos,e]

end HaarDerivedWreathCore
#print axioms HaarDerivedWreathCore.derived_next
