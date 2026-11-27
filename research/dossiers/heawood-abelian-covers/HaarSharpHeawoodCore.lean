import HaarSharpLamp
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace HaarSharpHeawood
abbrev S := ZMod 7
abbrev A := ZMod 239

def scale (s : S) : A := (10 : A)^s.val

theorem scale_add (s t : S) : scale (s+t) = scale s * scale t := by
  unfold scale
  rw [ZMod.val_add, ← pow_add]
  have w : (10 : A)^7 = 1 := by decide
  conv_rhs =>
    rw [← Nat.mod_add_div (s.val+t.val) 7, pow_add, pow_mul, w, one_pow, mul_one]

structure G where
  lamp : A
  shift : S

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

def port (i : Fin 3) : G :=
  if i=0 then 1 else if i=1 then ⟨0,1⟩ else ⟨1,3⟩

def key (a : G) : Nat := 239*a.shift.val+a.lamp.val

def coordinates : G ≃ A × S where
  toFun g := ⟨g.lamp,g.shift⟩
  invFun p := ⟨p.1,p.2⟩
  left_inv := by intro g; cases g; rfl
  right_inv := by intro p; cases p; rfl

instance : Finite G := Finite.of_equiv _ coordinates.symm

theorem cardinality : Nat.card G = 1673 := by
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

theorem distinct_ports : Function.Injective port := by
  have h : Function.Injective (fun i : Fin 3 => (port i).shift) := by decide +kernel
  exact fun _ _ e => h (congrArg G.shift e)

end HaarSharpHeawood
