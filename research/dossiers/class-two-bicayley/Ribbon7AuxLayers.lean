import Ribbon7AuxWords

namespace Ribbon7Aux
open HaarUniversal36 HaarClass5Commute
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem quotient_nil (n : Nat) :
    L (G ⧸ L G n) n = ⊥ := by
  let f := QuotientGroup.mk' (L G n)
  have M : (L G n).map f = L (G ⧸ L G n) n := by
    rw [Subgroup.map_lowerCentralSeries,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective _)]
  rw [←M,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']

theorem layer_with_first {n : Nat} {z w : G} (hz : z∈L G n) (hw : w∈L G 1) :
    ⁅z,w⁆∈L G (n+2) := by
  let N := L G (n+2)
  let f := QuotientGroup.mk' N
  have hm (j : Nat) : (L G j).map f=L (G ⧸ N) j := by
    rw [Subgroup.map_lowerCentralSeries,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective _)]
  have z' := hm n ▸ Subgroup.mem_map_of_mem f hz
  have w' := hm 1 ▸ Subgroup.mem_map_of_mem f hw
  have C : L (G ⧸ N) 1 ≤ Subgroup.centralizer ({f z}:Set (G ⧸ N)) := by
    change ⁅(⊤:Subgroup (G ⧸ N)),(⊤:Subgroup (G ⧸ N))⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (centralizes_commutator n (quotient_nil (G:=G) (n+2)) z' a b).symm.eq
  apply (QuotientGroup.eq_one_iff (N:=N) _).mp
  change f ⁅z,w⁆=1
  rw [map_commutatorElement]
  have E : Commute (f z) (f w) := (Subgroup.mem_centralizer_singleton_iff.mp (C w')).symm
  exact E.commutator_eq

theorem u_layer (x y : G) : U x y ∈ L G 1 := by
  change U x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one, ← Abelianization.ker_of]
  change Abelianization.of (U x y)=1
  simp only [U,map_mul,map_inv]
  let X := Abelianization.of x
  let Y := Abelianization.of y
  change X⁻¹*Y⁻¹*X*X*Y⁻¹*X⁻¹*Y*X⁻¹*Y*X=1
  calc
    _ = (X*X*X*X⁻¹*X⁻¹*X⁻¹)*(Y*Y*Y⁻¹*Y⁻¹) := by ac_rfl
    _ = 1 := by group

theorem res_layer_of (x y : G) {n : Nat} (H : h x y∈L G n) :
    res x y∈L G (n+2) := by
  have Q : q x y∈L G 1 := next (Subgroup.mem_top x) y⁻¹
  have E := (L G (n+2)).inv_mem (layer_with_first H Q)
  rw [commutatorElement_inv] at E
  rw [res_form]
  exact (inferInstance : (L G (n+2)).Normal).conj_mem _ E _

theorem z_layer_of (x y : G) {n : Nat} (H : h x y∈L G n) :
    Ribbon5Law.trace x y false wc∈L G (n+4) := by
  rw [w_end]
  have e : ⁅U x y,V x y⁆=(U x y)⁻¹*⁅U x y,res x y⁆*U x y := by
    simp only [res,commutatorElement_def]
    group
  have E := (L G (n+4)).inv_mem (layer_with_first (res_layer_of x y H) (u_layer x y))
  rw [commutatorElement_inv] at E
  rw [e]
  simpa only [inv_inv] using (inferInstance : (L G (n+4)).Normal).conj_mem _ E (U x y)⁻¹

theorem z_one_of_h_deep (nil : L G 7=⊥) (x y : G) (H : h x y∈L G 3) :
    Ribbon5Law.trace x y false wc=1 := by
  have E := z_layer_of x y H
  rw [show 3+4=7 from rfl,nil,Subgroup.mem_bot] at E
  exact E

end Ribbon7Aux
#print axioms Ribbon7Aux.z_one_of_h_deep
