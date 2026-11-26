import HaarClass5FiniteNoThree
import HaarClass6Odd

namespace HaarClass6Finite
open HaarAllNoncommuting HaarTwoKernel HaarClass4Generate HaarUniversal36
variable {G : Type*} [Group G]

theorem normalized [Finite G] (nil : L G 6=⊥)
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ j, 2≤j ∧ j≤6+Nat.factorization (Nat.card G) 2 ∧ HasCycle x y (2^j) := by
  classical
  let : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨6,nil⟩
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
  have cls : L (G ⧸ S) 6=⊥ := by
    have M : (L G 6).map f = L (G ⧸ S) 6 := map_ls f (QuotientGroup.mk'_surjective S) 6
    rw [← M,nil,Subgroup.map_bot]
  exact HaarClass5FiniteNoThree.lift_base f x y (card_two_bound f _ cardBound)
    (HaarClass6Odd.normalized cls odd (f x) (f y)) hx hy hxy

/-- The shortest dyadic cycle has length at most 64 times the Sylow 2-subgroup
order for any three distinct ports in a finite group of nilpotency class at most six. -/
theorem any_ports [Finite G] (nil : L G 6=⊥)
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ j, 2≤j ∧ j≤6+Nat.factorization (Nat.card G) 2 ∧ HaarAnyPorts.HasPortCycle r s t (2^j) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,el,eh,w⟩ := normalized nil (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,el,eh,HaarAnyPorts.map_cycle r s t w⟩

end HaarClass6Finite
#print axioms HaarClass6Finite.any_ports
