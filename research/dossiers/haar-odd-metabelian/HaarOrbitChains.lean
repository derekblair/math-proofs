import HaarOrbitVoltage

namespace HaarOrbitChains
open HaarOrbitVoltage
variable {E B A : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B] [AddCommGroup A]
variable {k : Nat}

def normalized (cot : Fin k → E) (w : Fin k → A) (e : E) : A :=
  ∑ i, if cot i=e then w i else 0

def coeffMap (w : Fin k → A) : (Fin k → ℤ) →+ A where
  toFun r := ∑ i, r i • w i
  map_zero' := by simp
  map_add' a b := by simp [add_zsmul,Finset.sum_add_distrib]

def push (ta : E → E) (c : E → ℤ) (e : E) : ℤ :=
  ∑ d, if ta d=e then c d else 0

theorem cotree_chain (cot : Fin k → E) (w : Fin k → A) (c : E → ℤ) :
    value c (normalized cot w) = coeffMap w (c ∘ cot) := by
  classical
  unfold value normalized
  change (∑ e, c e • ∑ i, if cot i=e then w i else 0) = ∑ i, c (cot i) • w i
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_ite,zsmul_zero]
  simp

theorem push_chain (ta : E → E) (c : E → ℤ) (w : E → A) :
    value (push ta c) w = value c (w ∘ ta) := by
  simpa [value,push,flux,Function.comp_def] using (sum_via_vertices ta c w).symm

theorem closure_of_chain (src dst : E → B) (cot : Fin k → E)
    (c : E → ℤ) (balanced : Balanced src dst c) (ta : E → E)
    (w : Fin k → A) (ψ : A →+ A) (p : B → A)
    (law : ∀ e, c e ≠ 0 → normalized cot w (ta e) =
      ψ (normalized cot w e) + p (dst e) - p (src e))
    (d z : Fin k → ℤ) (d_eq : c ∘ cot=d) (z_eq : push ta c ∘ cot=z)
    (zero : coeffMap w d=0) : coeffMap w z=0 := by
  rw [← d_eq,← cotree_chain] at zero
  rw [← z_eq,← cotree_chain,push_chain]
  exact translated_zero src dst c balanced _ _ ψ p law zero

end HaarOrbitChains
#print axioms HaarOrbitChains.closure_of_chain
