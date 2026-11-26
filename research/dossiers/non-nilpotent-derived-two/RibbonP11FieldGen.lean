import RibbonP11FieldRun

namespace RibbonP11
open HaarClass4Generate
universe u v
variable {G : Type u} [Group G] {K : Type v} [Field K]

/-- The affine multiplier pair determines the residue field of the prime
group algebra. An external field containing these multipliers may be
larger, but a surjective residue map cannot be. -/
theorem prime11_residue_generated (x y : G) (gen : Generates x y)
    (f : PA G 11→+*K) (surj : Function.Surjective f) (e : F→+*K)
    (a b : F) (hx : e a=f (gIn 11 x)) (hy : e b=f (gIn 11 y)) :
    Function.Surjective e := by
  let m : G→*Kˣ := (f.toMonoidHom.comp (gIn 11)).toHomUnits
  let H : Subgroup G :=
    { carrier := {g | ∃ s : F, e s=(m g:K)}
      one_mem' := ⟨1,by rw [map_one,map_one]; rfl⟩
      mul_mem' := by
        intro g h hg hh
        obtain ⟨r,hr⟩ := hg
        obtain ⟨s,hs⟩ := hh
        exact ⟨r*s,by rw [map_mul,hr,hs,map_mul,Units.val_mul]⟩
      inv_mem' := by
        intro g hg
        obtain ⟨r,hr⟩ := hg
        exact ⟨r⁻¹,by rw [map_inv₀,hr,map_inv,Units.val_inv_eq_inv_val]⟩ }
  have inc : Subgroup.closure ({x,y}:Set G) ≤ H := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl
    · exact ⟨a,hx⟩
    · exact ⟨b,hy⟩
  change Subgroup.closure ({x,y}:Set G)=⊤ at gen
  rw [gen] at inc
  have const : f.comp (algebraMap F (PA G 11)) = e := RingHom.ext_zmod _ _
  have L (z : PA G 11) : ∃ r : F, e r=f z := by
    induction z using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0,by rw [map_zero,map_zero]⟩
    | add z w hz hw =>
      obtain ⟨r,hr⟩ := hz
      obtain ⟨s,hs⟩ := hw
      exact ⟨r+s,by rw [map_add,hr,hs,map_add]⟩
    | single z r =>
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (commutator G) z
      have gg : g∈H := inc (Subgroup.mem_top g)
      obtain ⟨s,hs⟩ := gg
      refine ⟨r*s,?_⟩
      change e (r*s)=f (MonoidAlgebra.single (Abelianization.of g) r)
      rw [MonoidAlgebra.single_eq_algebraMap_mul_of,map_mul,map_mul,hs]
      have vc : f (algebraMap F (PA G 11) r)=e r := DFunLike.congr_fun const r
      rw [vc]
      rfl
  intro k
  obtain ⟨z,rfl⟩ := surj k
  exact L z

end RibbonP11
#print axioms RibbonP11.prime11_residue_generated
