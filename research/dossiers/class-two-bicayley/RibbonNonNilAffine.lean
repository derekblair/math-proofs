import HaarClass4Generate
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace RibbonNonNilAffine
abbrev S := ZMod 3
abbrev A := ZMod 7

def scale (s : S) : A := (2 : A)^s.val

theorem scale_add (s t : S) : scale (s+t) = scale s * scale t := by
  unfold scale
  rw [ZMod.val_add, ← pow_add]
  have w : (2 : A)^3 = 1 := by decide
  conv_rhs =>
    rw [← Nat.mod_add_div (s.val+t.val) 3, pow_add, pow_mul, w, one_pow, mul_one]

structure G where
  lamp : A
  shift : S
  deriving DecidableEq

def mul (a b : G) : G := ⟨a.lamp + scale a.shift*b.lamp, a.shift+b.shift⟩
def one : G := ⟨0,0⟩
def inv (a : G) : G := ⟨-(scale (-a.shift)*a.lamp), -a.shift⟩

@[ext] theorem G.ext' (a b : G) (hl : a.lamp = b.lamp) (hs : a.shift = b.shift) : a = b := by
  cases a; cases b; congr

theorem scale_zero : scale 0 = 1 := by rfl

instance : Group G where
  mul := mul
  one := one
  inv := inv
  mul_assoc := by
    intro a b c
    apply G.ext'
    · change (mul (mul a b) c).lamp = (mul a (mul b c)).lamp
      simp only [mul,scale_add,mul_add,mul_assoc,add_assoc]
    · change (mul (mul a b) c).shift = (mul a (mul b c)).shift
      simp [mul,add_assoc]
  one_mul := by
    intro a; apply G.ext'
    · change (mul one a).lamp = a.lamp; simp [mul,one,scale_zero]
    · change (mul one a).shift = a.shift; simp [mul,one]
  mul_one := by
    intro a; apply G.ext'
    · change (mul a one).lamp = a.lamp; simp [mul,one]
    · change (mul a one).shift = a.shift; simp [mul,one]
  inv_mul_cancel := by
    intro a; apply G.ext'
    · change (mul (inv a) a).lamp = one.lamp; simp [mul,inv,one]
    · change (mul (inv a) a).shift = one.shift; simp [mul,inv,one]

def coordinates : G ≃ A × S where
  toFun g := ⟨g.lamp,g.shift⟩
  invFun p := ⟨p.1,p.2⟩
  left_inv := by intro g; cases g; rfl
  right_inv := by intro p; cases p; rfl

instance : Finite G := Finite.of_equiv _ coordinates.symm

theorem cardinality : Nat.card G = 21 := by
  rw [Nat.card_congr coordinates, Nat.card_prod]
  simp [ZMod.card]

theorem odd : Odd (Nat.card G) := by rw [cardinality]; decide

def projection : G →* Multiplicative S where
  toFun g := Multiplicative.ofAdd g.shift
  map_one' := rfl
  map_mul' _ _ := rfl

theorem metabelian : ∀ a b : commutator G, a*b=b*a := by
  intro a b
  have ha := Abelianization.commutator_subset_ker projection a.property
  have hb := Abelianization.commutator_subset_ker projection b.property
  change a.val.shift = 0 at ha
  change b.val.shift = 0 at hb
  apply Subtype.ext
  apply G.ext'
  · change (mul a.val b.val).lamp = (mul b.val a.val).lamp
    simp [mul,ha,hb,scale_zero,add_comm]
  · change (mul a.val b.val).shift = (mul b.val a.val).shift
    simp [mul,ha,hb]


open HaarClass4Structure
open scoped commutatorElement

def a : G := ⟨0,1⟩
def b : G := ⟨1,0⟩

theorem nontriv : b≠1 := by decide +kernel

theorem keep : ⁅b⁻¹,a⁆=b := by decide +kernel

theorem every_layer (n : Nat) : b∈LS G n := by
  induction n with
  | zero => simp [LS]
  | succ n ih =>
    rw [← keep]
    exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ih) (Subgroup.mem_top a)

theorem not_nil (n : Nat) : LS G n≠⊥ := by
  intro e
  have hb := every_layer n
  rw [e,Subgroup.mem_bot] at hb
  exact nontriv hb

theorem normal_form : ∀ u : A, ∀ v : S,
    b^u.val*a^v.val=G.mk u v := by decide +kernel

end RibbonNonNilAffine
#print axioms RibbonNonNilAffine.not_nil
