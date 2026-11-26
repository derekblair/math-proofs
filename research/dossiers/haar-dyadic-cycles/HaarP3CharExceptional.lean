import HaarP3CharKernel

namespace HaarP3Char
open HaarClass4Structure HaarP3LayerGen
variable {G : Type*} [Group G]

theorem exception_relations {S : Subgroup G} (central : S ≤ Subgroup.center G)
    (cube : ∀ w∈S, w^(3:ℕ)=1) (P Q T0 T1 T2 : S)
    (hgen : S = Subgroup.closure ({P.val,Q.val} : Set G)) (nontriv : S≠⊥)
    (hχ : ∀ χ : S →* C3, χ ≠ 1 →
      χ Q=(χ P)⁻¹ ∧ χ T0=(χ P)⁻¹ ∧ χ T1=(χ P)⁻¹ ∧ χ T2=(χ P)⁻¹) :
    Q=P⁻¹ ∧ T0=P⁻¹ ∧ T1=P⁻¹ ∧ T2=P⁻¹ ∧ P≠1 ∧
    S=Subgroup.zpowers P.val ∧ orderOf P.val=3 ∧ Nat.card S=3 := by
  have q : Q=P⁻¹ :=
    separated_equal central cube Q P⁻¹ (fun χ h => (hχ χ h).1.trans (map_inv χ P).symm)
  have t0 : T0=P⁻¹ :=
    separated_equal central cube T0 P⁻¹ (fun χ h => (hχ χ h).2.1.trans (map_inv χ P).symm)
  have t1 : T1=P⁻¹ :=
    separated_equal central cube T1 P⁻¹ (fun χ h => (hχ χ h).2.2.1.trans (map_inv χ P).symm)
  have t2 : T2=P⁻¹ :=
    separated_equal central cube T2 P⁻¹ (fun χ h => (hχ χ h).2.2.2.trans (map_inv χ P).symm)
  have span : S=Subgroup.zpowers P.val := by
    refine hgen.trans ?_
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · rw [congrArg Subtype.val q]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    · rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.closure_mono (by simp)
  obtain ⟨ord,card,_⟩ := layer_order_and_powers S span nontriv (cube _ P.property)
  have hp : P≠1 := by
    intro h
    have hp' : P.val=1 := congrArg Subtype.val h
    rw [hp',orderOf_one] at ord
    omega
  exact ⟨q,t0,t1,t2,hp,span,ord,card⟩

theorem nontrivial_char_injective {S : Subgroup G} (size : Nat.card S=3)
    (χ : S →* C3) (ne : χ ≠ 1) : Function.Injective χ := by
  have ker : χ.ker=⊥ := by
    let : Fact ((Nat.card S).Prime) := ⟨size ▸ (by decide : Nat.Prime 3)⟩
    rcases χ.ker.eq_bot_or_eq_top_of_prime_card with h | h
    · exact h
    · exact False.elim (ne (by
        ext x
        have t : x∈χ.ker := h.symm ▸ Subgroup.mem_top x
        exact MonoidHom.mem_ker.mp t))
  exact (MonoidHom.ker_eq_bot_iff χ).mp ker

end HaarP3Char

#print axioms HaarP3Char.exception_relations
#print axioms HaarP3Char.nontrivial_char_injective
