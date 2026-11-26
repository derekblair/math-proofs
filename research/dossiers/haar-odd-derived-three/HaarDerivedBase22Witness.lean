import HaarDerivedBarbellCert

namespace HaarDerivedBase22Witness
open HaarDerivedBarbell HaarAllNoncommuting
open HaarDerivedWreathTrace HaarSharpPortGeometry

private def rowCode (i : Fin 22) : Bool × Nat :=
  ((base i.val).1, HaarDerivedGirth22.key (base i.val).2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem rowCode_nodup : (List.ofFn rowCode).Nodup := by decide +kernel

private theorem injective : Function.Injective (fun i : Fin 22 => base i.val) := by
  intro i j eq
  apply List.nodup_ofFn.mp rowCode_nodup
  exact congrArg (fun b : Bool × Q => (b.1,HaarDerivedGirth22.key b.2)) eq

private theorem base_step (a : Bool × Q) (j : Fin 3) :
    HaarCycle.haarAdj x y a (step x y a j) := by
  rcases a with ⟨p,a⟩
  cases p <;> fin_cases j <;> simp [HaarCycle.haarAdj,step,oriented,basePort,mul_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem cycle22 : HasCycle x y 22 := by
  refine ⟨fun i => base i.val, injective,?_⟩
  intro i
  have e : base (i.val+1) = step x y (base i.val) (code i.val) :=
    (good_row i.val (by omega)).1
  have H := base_step (base i.val) (code i.val)
  rw [←e] at H
  by_cases hop : i.val+1<22
  · simpa only [Nat.mod_eq_of_lt hop] using H
  · have E : i.val+1=22 := by omega
    have closed : base 22 = base 0 := base22.trans base0.symm
    rw [E,closed] at H
    simpa only [E,Nat.mod_self] using H

end HaarDerivedBase22Witness
#print axioms HaarDerivedBase22Witness.cycle22
