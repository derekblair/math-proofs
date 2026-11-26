import HaarDerivedWreathCore

namespace HaarDerivedWreathExactClass
open HaarDerivedWreathCore
open scoped commutatorElement
variable {Q : Type*} [Group Q] [DecidableEq Q]

def purePos : Q →* W Q where
  toFun q := ⟨fun _ _ => 0,q⟩
  map_one' := by rfl
  map_mul' a b := by
    apply W.ext'
    · intro t i; change (0 : ZMod 3) = 0+0; simp
    · rfl

@[simp] theorem pos_pure (d : Q) : (purePos d).pos=d := rfl
@[simp] theorem lamp_pure (d : Q) (b : Bool) (r : Q) : (purePos d).lamp b r=0 := rfl

def lampOne : W Q := ⟨atPos false 1,1⟩

def diffLamp (d : Q) : W Q := ⁅purePos d,lampOne⁆

theorem diff_values (d : Q) (q : Q) :
    (diffLamp d).lamp false q = (if d=q then 1 else 0) - (if q=1 then 1 else 0) := by
  unfold diffLamp
  rw [commutatorElement_def]
  change (mul (mul (mul (purePos d) lampOne) (inv (purePos d))) (inv lampOne)).lamp false q = _
  have E : 1=d⁻¹*q ↔ d=q := by
    rw [eq_comm,inv_mul_eq_one]
  have E' : d⁻¹*q=1 ↔ d=q := eq_comm.trans E
  simp [mul,inv,lampOne,atPos,E,E',sub_eq_add_neg,eq_comm]

theorem not_commute (d : Q) (hd : d≠1) : ¬ Commute (purePos d) (diffLamp d) := by
  intro c
  have eq := congrArg (fun w : W Q => w.lamp false d) c.eq
  change (mul (purePos d) (diffLamp d)).lamp false d =
    (mul (diffLamp d) (purePos d)).lamp false d at eq
  simp [mul,diff_values,hd,show 1≠d from Ne.symm hd] at eq
  exact (by decide : (-1 : ZMod 3) ≠ 1) eq

theorem derived_not_two (x y : Q) (ncomm : ¬ Commute x y) :
    derivedSeries (W Q) 2 ≠ ⊥ := by
  let d := ⁅x,y⁆
  have hd : d≠1 := by
    intro D
    exact ncomm (commutatorElement_eq_one_iff_commute.mp D)
  have p : (purePos d : W Q) ∈ derivedSeries (W Q) 1 := by
    rw [show (purePos d : W Q) = ⁅purePos x,purePos y⁆ from map_commutatorElement purePos x y]
    rw [show (1:ℕ)=0+1 by rfl,derivedSeries_succ,derivedSeries_zero]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have l : diffLamp d ∈ derivedSeries (W Q) 1 := by
    rw [show (1:ℕ)=0+1 by rfl,derivedSeries_succ,derivedSeries_zero]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have w : ⁅purePos d,diffLamp d⁆ ∈ derivedSeries (W Q) 2 := by
    rw [show (2:ℕ)=1+1 by rfl,derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator p l
  intro zero
  rw [zero] at w
  exact not_commute d hd (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp w))

theorem exact_three (x y : Q) (ncomm : ¬ Commute x y) (met : derivedSeries Q 2=⊥) :
    derivedSeries (W Q) 2≠⊥ ∧ derivedSeries (W Q) 3=⊥ :=
  ⟨derived_not_two x y ncomm,derived_next 2 met⟩

end HaarDerivedWreathExactClass
#print axioms HaarDerivedWreathExactClass.exact_three
