import TightParity

namespace FolkmanB4.Tight
open Critical
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq V]

theorem sign_agree {W Z : Type*} [Fintype W] [DecidableEq W]
    (k s t : W ≃ Z) (delta : Equiv.Perm.sign (s.trans t.symm)=1) :
    Equiv.Perm.sign (s.trans k.symm)=Equiv.Perm.sign (t.trans k.symm) := by
  let a := s.trans k.symm
  let b := t.trans k.symm
  have E : s.trans t.symm=a.trans b.symm := by ext x; simp [a,b]
  rw [E,Equiv.Perm.sign_trans] at delta
  change Equiv.Perm.sign (b⁻¹) * Equiv.Perm.sign a = 1 at delta
  rw [map_inv,mul_comm] at delta
  exact mul_inv_eq_one.mp delta

/-- The tight-contraction signing can be concentrated at its port.
Every signed perfect-matching term has the same (positive) parity. -/
theorem port_signing (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (covered : Covered I) (tight : Tight I A B) (k : V ≃ L)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm))
    (base : Option (In B) ≃ In A) :
    ∃ u : In A → ℤˣ, ∀ q : Option (In B) ≃ In A,
      (∀ i, pointsContraction I A B (q i) i) →
      Equiv.Perm.sign (q.trans base.symm) * u (q none) = 1 := by
  classical
  let P (l : In A) := ∃ q : Option (In B) ≃ In A, q none=l ∧
    ∀ i, pointsContraction I A B (q i) i
  let U (l : In A) : ℤˣ := if h : P l then
      (Equiv.Perm.sign (h.choose.trans base.symm))⁻¹ else 1
  refine ⟨U,fun q h => ?_⟩
  have hp : P (q none) := ⟨q,rfl,h⟩
  let r := hp.choose
  have rOK := hp.choose_spec
  have d := quotient_fixed_port_parity I A B covered tight k signs q r h
    rOK.2 rOK.1.symm
  have agree := sign_agree base q r d
  rw [agree]
  simp [U,hp,r]

#print axioms port_signing
end FolkmanB4.Tight
