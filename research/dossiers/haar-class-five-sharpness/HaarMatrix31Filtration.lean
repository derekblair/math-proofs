import HaarAnyPorts
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Nilpotent.Basic

namespace HaarMatrix31Filtration

open scoped commutatorElement

abbrev Mat := Matrix (Fin 6) (Fin 6) (ZMod 31)

def Band (k : ℕ) (A : Mat) : Prop := ∀ i j : Fin 6, j.val < i.val+k → A i j=0

theorem band_zero (k : ℕ) : Band k 0 := by intro i j _; rfl

theorem band_add {k : ℕ} {A B : Mat} (a : Band k A) (b : Band k B) :
    Band k (A+B) := by
  intro i j h
  simp [a i j h,b i j h]

theorem band_sub {k : ℕ} {A B : Mat} (a : Band k A) (b : Band k B) :
    Band k (A-B) := by
  intro i j h
  simp [a i j h,b i j h]

theorem band_mono {i j : ℕ} (h : i ≤ j) {A : Mat} (a : Band j A) : Band i A :=
  fun x y z => a x y (by omega)

theorem band_mul {k l : ℕ} {A B : Mat} (a : Band k A) (b : Band l B) :
    Band (k+l) (A*B) := by
  intro i j h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases e : r.val < i.val+k
  · rw [a i r e,zero_mul]
  · rw [b r j (by omega),mul_zero]

theorem band_six {A : Mat} (a : Band 6 A) : A=0 := by
  ext i j
  exact a i j (by have := j.isLt; omega)

theorem band_one_pow {A : Mat} (a : Band 1 A) (k : ℕ) : Band k (A^k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    intro i j lt
    rw [Matrix.one_apply_ne]
    intro e
    subst j
    omega
  | succ k ih =>
    rw [pow_succ]
    exact band_mul ih a

theorem unit_add {A : Mat} (a : Band 1 A) : IsUnit (1+A) :=
  IsNilpotent.isUnit_one_add ⟨6,band_six (band_one_pow a 6)⟩

instance finiteUnits : Finite Matˣ := Finite.of_injective _ Units.val_injective

def positiveMonoid (k : ℕ) : Submonoid Matˣ where
  carrier := {u | Band k ((u:Mat)-1)}
  one_mem' := by simp only [Set.mem_setOf_eq,Units.val_one,sub_self]; exact band_zero k
  mul_mem' := by
    intro a b ha hb
    change Band k ((a:Mat)-1) at ha
    change Band k ((b:Mat)-1) at hb
    change Band k ((a:Mat)*(b:Mat)-1)
    rw [show (a:Mat)*(b:Mat)-1 = ((a:Mat)-1)*((b:Mat)-1)+((a:Mat)-1)+((b:Mat)-1) by noncomm_ring]
    exact band_add (band_add (band_mono (by omega) (band_mul ha hb)) ha) hb

theorem positive_inv (k : ℕ) {x : Matˣ} (hx : x ∈ positiveMonoid k) :
    x⁻¹ ∈ positiveMonoid k := by
  have z : x ^ (orderOf x - 1) * x=1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  have q : x ^ (orderOf x - 1)=x⁻¹ := by
    apply mul_right_cancel (b:=x)
    rw [z,inv_mul_cancel]
  rw [← q]
  exact (positiveMonoid k).pow_mem hx _

def upper (k : ℕ) : Subgroup Matˣ :=
  { positiveMonoid k with inv_mem' := fun hx => positive_inv k hx }

theorem mem_upper {k : ℕ} {a : Matˣ} : a∈upper k ↔ Band k ((a:Mat)-1) := Iff.rfl

theorem upper_anti {i j : ℕ} (h : i ≤ j) : upper j ≤ upper i :=
  fun _ hz => band_mono h hz

theorem upper_six : upper 6=⊥ := by
  apply le_bot_iff.mp
  intro a ha
  have e : (a:Mat)-1=0 := band_six ha
  exact Subgroup.mem_bot.mpr (Units.ext (sub_eq_zero.mp e))

theorem bracket_upper {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ⁅upper i,upper j⁆ ≤ upper (i+j) := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have X := mem_upper.mp hx
  have Y := mem_upper.mp hy
  have inv : (y*x)⁻¹ ∈ upper 1 := (upper 1).inv_mem ((upper 1).mul_mem (upper_anti hj hy) (upper_anti hi hx))
  have invB := mem_upper.mp inv
  have diff : Band (i+j) ((x:Mat)*(y:Mat)-(y:Mat)*(x:Mat)) := by
    rw [show (x:Mat)*(y:Mat)-(y:Mat)*(x:Mat) =
      ((x:Mat)-1)*((y:Mat)-1)-((y:Mat)-1)*((x:Mat)-1) by noncomm_ring]
    exact band_sub (band_mul X Y) (by simpa only [Nat.add_comm j i] using band_mul Y X)
  have formula : (↑⁅x,y⁆:Mat)-1 = ((x:Mat)*(y:Mat)-(y:Mat)*(x:Mat))* (↑((y*x)⁻¹):Mat) := by
    rw [sub_mul]
    have hxy : ((y:Mat)*(x:Mat)) * (↑((y*x)⁻¹):Mat)=1 := by
      rw [← Units.val_mul, ← Units.val_mul,mul_inv_cancel,Units.val_one]
    rw [hxy]
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, mul_inv_rev, Units.val_mul,mul_assoc]
  apply mem_upper.mpr
  rw [formula]
  generalize (x:Mat)*(y:Mat)-(y:Mat)*(x:Mat)=Z at *
  rw [show Z*(↑((y*x)⁻¹):Mat) = Z+Z*((↑((y*x)⁻¹):Mat)-1) by noncomm_ring]
  exact band_add diff (band_mono (by omega) (band_mul diff invB))

theorem lower_band (k : ℕ) : (upper 1).lowerCentralSeries k ≤ upper (k+1) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    exact (Subgroup.commutator_mono ih le_rfl).trans
      (by simpa [Nat.add_assoc] using (bracket_upper (i:=k+1) (j:=1) (by omega) (by decide)))

theorem class_at_most_five : (⊤ : Subgroup (upper 1)).lowerCentralSeries 5=⊥ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.top_subtype_lowerCentralSeries,Subgroup.map_bot,← le_bot_iff,← upper_six]
  exact lower_band 5

end HaarMatrix31Filtration

#print axioms HaarMatrix31Filtration.class_at_most_five
