import RibbonP11LocalJet

namespace RibbonP11
variable {K S : Type*} [Field K] [CommRing S] [Nontrivial S] [Algebra K S] [Finite S]

/-- If all simple residues of a finite algebra are the base field, there
are either two distinct residue characters, a genuine first jet, or the
entire algebra is already the base field. -/
theorem field_pair_or_jet
    (res : ∀ I : Ideal S, I.IsMaximal →
      ∃ f : S →ₐ[K] K, RingHom.ker f.toRingHom=I) :
    (∃ f : S →ₐ[K] K, Function.Injective f) ∨
      (∃ f g : S →ₐ[K] K, f≠g) ∨
      (∃ (f : S →ₐ[K] K) (δ : S →ₗ[K] K),
        (∀ r s : S, δ (r*s)=f r*δ s+δ r*f s) ∧
        Function.Surjective (fun r => (f r,δ r))) := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal S
  obtain ⟨f,hf⟩ := res I hI
  by_cases un : ∀ J : Ideal S, J.IsMaximal → J=I
  · rcases local_field_or_jet f (fun J hJ => (un J hJ).trans hf.symm) with h | ⟨δ,der,surj⟩
    · exact Or.inl ⟨f,h⟩
    · exact Or.inr (Or.inr ⟨f,δ,der,surj⟩)
  · push_neg at un
    obtain ⟨J,hJ,ne⟩ := un
    obtain ⟨g,hg⟩ := res J hJ
    refine Or.inr (Or.inl ⟨f,g,?_⟩)
    intro e
    apply ne
    exact hg.symm.trans (e ▸ hf)

end RibbonP11
#print axioms RibbonP11.field_pair_or_jet
