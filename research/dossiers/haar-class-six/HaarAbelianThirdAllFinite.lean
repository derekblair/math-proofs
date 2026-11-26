import HaarAbelianThirdAllOdd
import HaarAbelianThirdFinite

namespace HaarAbelianThirdAllFinite
open HaarUniversal36 HaarAllNoncommuting HaarAbelianThirdOdd HaarTwoKernel HaarClass4Generate
variable {G : Type*} [Group G]

theorem normalized [Finite G] (nil : ∃ n, L G n=⊥) (ab : AbelianThird G)
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ j, 2≤j ∧ j≤6+Nat.factorization (Nat.card G) 2 ∧ HasCycle x y (2^j) := by
  classical
  let : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr nil
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Classical.arbitrary _
  let S : Subgroup G := P
  let : S.Normal := by change (P : Subgroup G).Normal; infer_instance
  let f := QuotientGroup.mk' S
  have cardBound : Nat.card f.ker ∣ 2^Nat.factorization (Nat.card G) 2 := by
    change Nat.card (QuotientGroup.mk' S).ker ∣ _
    rw [QuotientGroup.ker_mk']
    exact (P.card_eq_multiplicity).dvd
  have odd : Odd (Nat.card (G ⧸ S)) := by
    rw [← Nat.not_even_iff_odd,even_iff_two_dvd,← S.index_eq_card]
    exact P.not_dvd_index
  have cls : ∃ n, L (G ⧸ S) n=⊥ := by
    obtain ⟨n,h⟩ := nil
    refine ⟨n,?_⟩
    have m : (L G n).map f=L (G ⧸ S) n := map_ls f (QuotientGroup.mk'_surjective S) n
    rw [←m,h,Subgroup.map_bot]
  exact HaarClass5FiniteNoThree.lift_base f x y (card_two_bound f _ cardBound)
    (HaarAbelianThirdAllOdd.normalized cls (HaarAbelianThirdFinite.abelian_map f (QuotientGroup.mk'_surjective S) ab)
      odd (f x) (f y)) hx hy hxy

theorem any_ports [Finite G] (nil : ∃ n, L G n=⊥) (ab : AbelianThird G)
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ j, 2≤j ∧ j≤6+Nat.factorization (Nat.card G) 2 ∧ HaarAnyPorts.HasPortCycle r s t (2^j) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,lo,hi,cy⟩ := normalized nil ab (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,lo,hi,HaarAnyPorts.map_cycle r s t cy⟩

/-- The derived subgroup is abelian when the group is metabelian. -/
def CommutingDerived (G : Type*) [Group G] : Prop :=
  ∀ a b : G, a∈L G 1 → b∈L G 1 → Commute a b

theorem metabelian [Finite G] (nil : ∃ n, L G n=⊥)
    (met : CommutingDerived G)
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ j, 2≤j ∧ j≤6+Nat.factorization (Nat.card G) 2 ∧ HaarAnyPorts.HasPortCycle r s t (2^j) := by
  have hi : L G 2≤L G 1 := Subgroup.lowerCentralSeries_antitone _ (by decide : 1≤2)
  exact any_ports nil (fun a b ha hb => met a b (hi ha) (hi hb)) r s t hr ht hs

end HaarAbelianThirdAllFinite
#print axioms HaarAbelianThirdAllFinite.any_ports
#print axioms HaarAbelianThirdAllFinite.metabelian
