import HaarHalfCollision
import HaarClassFourFinite

namespace HaarUniversal36
open scoped commutatorElement
open HaarHalfCollision
variable {G : Type*} [Group G]

abbrev L (G : Type*) [Group G] (i : ℕ) : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries i

theorem next {i : ℕ} {z : G} (hz : z ∈ L G i) (w : G) :
    ⁅z,w⁆ ∈ L G (i+1) :=
  Subgroup.commutator_mem_commutator hz (Subgroup.mem_top w)

theorem strip (a b c d : G) (hc : ∀ k : G, Commute c k) (hd : ∀ k : G, Commute d k) :
    ⁅c*a,d*b⁆ = ⁅a,b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, (hc (d*b)).commutator_eq,mul_one,
    (hc _).eq,mul_inv_cancel_right,commutatorElement_mul_right_eq_mul_conj,
    (hd a).symm.commutator_eq,one_mul,(hd _).eq,mul_inv_cancel_right]

theorem class5_centralizes_commutator (nil : L G 5=⊥) {z : G}
    (hz : z ∈ L G 3) (a b : G) : Commute z ⁅a,b⁆ := by
  have hc (v w : G) : Commute ⁅z,v⁆ w := by
    apply commutatorElement_eq_one_iff_commute.mp
    have hh := next (next hz v) w
    change ⁅⁅z,v⁆,w⁆ ∈ L G 5 at hh
    rw [nil] at hh
    exact Subgroup.mem_bot.mp hh
  have h : z * ⁅a,b⁆ * z⁻¹ = ⁅a,b⁆ := by
    rw [conjugate_commutatorElement]
    change ⁅MulAut.conj z a,MulAut.conj z b⁆ = _
    rw [conj_eq_commutatorElement_mul,conj_eq_commutatorElement_mul]
    exact strip a b _ _ (hc a) (hc b)
  exact mul_inv_eq_iff_eq_mul.mp h

def z (x y : G) (i : ℕ) : G := x^i*y*(x^i)⁻¹

def a (x y : G) : G := (z x y 0)⁻¹ * z x y 1
def b (x y : G) : G := (z x y 1)⁻¹ * z x y 2
def c (x y : G) : G := (z x y 2)⁻¹ * z x y 3

theorem b_conj (x y : G) : b x y = x * a x y * x⁻¹ := by
  simp only [a,b,z,pow_zero,pow_one,pow_succ]
  group

theorem c_conj (x y : G) : c x y = x * b x y * x⁻¹ := by
  simp only [b,c,z,pow_zero,pow_one,pow_succ]
  group
  simp [zpow_ofNat,pow_two]

theorem a_comm (x y : G) : a x y = ⁅y⁻¹,x⁆ := by
  simp [a,z,commutatorElement_def,mul_assoc]

theorem b_comm (x y : G) : b x y = ⁅(z x y 1)⁻¹,x⁆ := by
  simp only [b,z,commutatorElement_def,pow_one,pow_succ]
  group

theorem correction (x y : G) : c x y * a x y * ((b x y)^2)⁻¹ ∈ L G 3 := by
  let a' := a x y
  let b' := b x y
  let c' := c x y
  let d := a'⁻¹*b'
  let e := b'⁻¹*c'
  have ha : a' ∈ L G 1 := by
    change a x y ∈ L G 1
    rw [a_comm]
    exact next (Subgroup.mem_top _) _
  have d_comm : d = ⁅a'⁻¹,x⁆ := by
    change a'⁻¹ * b x y = _
    rw [b_conj]
    simp [a',commutatorElement_def,mul_assoc]
  have hd : d ∈ L G 2 := by rw [d_comm]; exact next ((L G 1).inv_mem ha) _
  have ec : e = x*d*x⁻¹ := by
    change (b x y)⁻¹ * c x y = x * ((a x y)⁻¹*b x y)*x⁻¹
    rw [c_conj,b_conj]
    group
  let Q := L G 3
  let f := QuotientGroup.mk' Q
  have cd (u : G) : Commute (f d) (f u) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := Q) _).mpr (next hd u)
  have ede : f e = f d := by
    rw [ec,map_mul,map_mul,map_inv,(cd x).symm.eq,mul_inv_cancel_right]
  have eb : f b' = f a' * f d := by simp [d,mul_assoc]
  have ee : f c' = f b' * f e := by simp [e,mul_assoc]
  have eq : (f c') * (f a') = (f b')^2 := by
    rw [ee,ede,eb,pow_two,mul_assoc,(cd a').eq]
  apply (QuotientGroup.eq_one_iff (N := Q) _).mp
  change f (c'*a'*(b'^2)⁻¹) = 1
  rw [map_mul,map_mul,map_inv,map_pow,eq,mul_inv_cancel]

theorem ca_commute (nil : L G 5=⊥) (x y : G) : Commute (c x y * a x y) (b x y) := by
  let k := c x y * a x y * ((b x y)^2)⁻¹
  have hm : k ∈ L G 3 := correction x y
  have h : Commute k (b x y) := by
    rw [b_comm]
    exact class5_centralizes_commutator nil hm _ _
  have e : c x y*a x y = k*(b x y)^2 := by simp [k,mul_assoc]
  rw [e]
  exact h.mul_left ((Commute.refl _).pow_left _)

def word : List (Fin 3) :=
  [0,2,1,0,2,0,1,2,0,1,0,1,2,0,1,0,1,0,1,2,0,1,2,1,0,2,1,0,1,0,2,1,0,1,0,1]

theorem word_value (x y : G) : prodFrom x y 0 word =
    a x y * (b x y)⁻¹ * (a x y)⁻¹ * (c x y)⁻¹ * b x y * c x y := by
  norm_num [word,prodFrom,signPort,port,a,b,c,z,pow_succ]
  group

theorem word_closes (nil : L G 5=⊥) (x y : G) : prodFrom x y 0 word = 1 := by
  rw [word_value]
  have e := (ca_commute nil x y).eq
  have r : c x y * a x y * (b x y)⁻¹ = (b x y)⁻¹ * (c x y * a x y) :=
    (ca_commute nil x y).inv_right.eq
  calc
    _ = (c x y)⁻¹ * (c x y*a x y*(b x y)⁻¹) * (a x y)⁻¹ *
        (c x y)⁻¹ * b x y * c x y := by group
    _ = 1 := by rw [r]; group

theorem word_good : HaarSharpCore.good word = true := by decide
theorem word_len : word.length=36 := by decide

end HaarUniversal36
#print axioms HaarUniversal36.word_closes
