import RibbonP11Jet
import Mathlib.RingTheory.Nakayama

namespace RibbonP11
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S] [Finite S]

/-- Over the prime field, one residue character and a nontrivial kernel
force a genuine first jet. The kernel square cannot equal the kernel
by Nakayama's lemma. -/
theorem local_field_or_jet (f : S →ₐ[K] K)
    (unique : ∀ I : Ideal S, I.IsMaximal → I=RingHom.ker f.toRingHom) :
    Function.Injective f ∨
    ∃ δ : S →ₗ[K] K,
      (∀ r s : S, δ (r*s)=f r*δ s+δ r*f s) ∧
      Function.Surjective (fun r => (f r,δ r)) := by
  classical
  let J := RingHom.ker f.toRingHom
  by_cases Z : J=⊥
  · left
    exact (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr Z
  · right
    have jac : J ≤ (⊥ : Ideal S).jacobson := by
      change J ≤ sInf {I : Ideal S | ⊥ ≤ I ∧ I.IsMaximal}
      apply le_sInf
      intro I hI
      exact (unique I hI.2).ge
    have fg : J.FG := by
      change Submodule.FG (J : Submodule S S)
      rw [Submodule.fg_def]
      exact ⟨J,Set.toFinite _,Submodule.span_eq _⟩
    have H : ¬ J ≤ J^2 := by
      intro h
      apply Z
      apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J J fg _ jac
      rw [Ideal.smul_eq_mul,←pow_two]
      exact h
    obtain ⟨w,hw,fresh⟩ := SetLike.not_le_iff_exists.mp H
    obtain ⟨δ,_,der,surj⟩ := cotangent_jet f w hw fresh
    exact ⟨δ,der,surj⟩

end RibbonP11
#print axioms RibbonP11.local_field_or_jet
