import HaarClass6Commute

namespace HaarClass6RankOneStructure
open HaarUniversal36 HaarClass6Commute
variable {G : Type*} [Group G]

theorem gamma3_abelian (nil : L G 6=⊥) (u : G)
    (span : let f := QuotientGroup.mk' (L G 3)
      (L G 2).map f = Subgroup.zpowers (f u))
    {a b : G} (ha : a ∈ L G 2) (hb : b ∈ L G 2) : Commute a b := by
  let f := QuotientGroup.mk' (L G 3)
  change (L G 2).map f = _ at span
  have hu : u ∈ L G 2 := by
    have hf : f u ∈ (L G 2).map f := by
      rw [span]; exact Subgroup.mem_zpowers _
    obtain ⟨v,hv,eq⟩ := hf
    have hq : v⁻¹*u ∈ L G 3 := (QuotientGroup.eq_one_iff _).mp (by
      change f (v⁻¹*u)=1
      rw [map_mul,map_inv,eq,inv_mul_cancel])
    have hle : L G 3 ≤ L G 2 :=
      Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by decide : 2 ≤ 3)
    have hh := Subgroup.mul_mem _ hv (hle hq)
    simpa [← mul_assoc] using hh
  have decomp (z : G) (hz : z ∈ L G 2) :
      ∃ i : ℤ, ∃ t ∈ L G 3, z=u^i*t := by
    have h := Subgroup.mem_map_of_mem f hz
    rw [span] at h
    obtain ⟨i,eq⟩ := Subgroup.mem_zpowers_iff.mp h
    refine ⟨i,(u^i)⁻¹*z,?_,by group⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change f ((u^i)⁻¹*z)=1
    rw [map_mul,map_inv,map_zpow,eq,inv_mul_cancel]
  obtain ⟨i,s,hs,ea⟩ := decomp a ha
  obtain ⟨j,t,ht,eb⟩ := decomp b hb
  have hp : Commute (u^i) b := by
    rw [eb]
    exact (((Commute.refl u).zpow_left i).zpow_right j).mul_right
      ((central_L2 3 nil ht hu).symm.zpow_left i)
  rw [ea]
  exact hp.mul_left (central_L2 3 nil hs hb)

end HaarClass6RankOneStructure
#print axioms HaarClass6RankOneStructure.gamma3_abelian
