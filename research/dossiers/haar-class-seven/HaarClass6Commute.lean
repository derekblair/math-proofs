import HaarClass5L2Abelian

namespace HaarClass6Commute
open HaarUniversal36 HaarClass5Commute HaarClass5L2Abelian
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem delta_L1 (i : ℕ) {z a : G} (hz : z ∈ L G i) (ha : a ∈ L G 1) :
    ⁅z,a⁆ ∈ L G (i+2) := by
  let Q := L G (i+2)
  let f := QuotientGroup.mk' Q
  have hm (i : ℕ) : (L G i).map f = L (G ⧸ Q) i := by
    rw [Subgroup.map_lowerCentralSeries,Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective Q)]
  have nil : L (G ⧸ Q) (i+2)=⊥ := by
    rw [← hm (i+2),Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have hz' : f z ∈ L (G ⧸ Q) i := hm i ▸ Subgroup.mem_map_of_mem f hz
  have ha' : f a ∈ L (G ⧸ Q) 1 := hm 1 ▸ Subgroup.mem_map_of_mem f ha
  apply (QuotientGroup.eq_one_iff (N:=Q) _).mp
  change f ⁅z,a⁆=1
  rw [map_commutatorElement,(central_L1 i nil hz' ha').commutator_eq]

theorem central_gen_L2 (i : ℕ) (nil : L G (i+3)=⊥) {z a : G} (hz : z ∈ L G i)
    (ha : a ∈ L G 1) (b : G) : Commute z ⁅a,b⁆ := by
  let u := ⁅z,a⁆
  let v := ⁅z,b⁆
  have uc (w : G) : Commute u w := by
    apply commutatorElement_eq_one_iff_commute.mp
    have h := next (delta_L1 i hz ha) w
    change ⁅u,w⁆ ∈ L G (i+3) at h
    rw [nil] at h
    exact Subgroup.mem_bot.mp h
  have hv : v ∈ L G (i+1) := next hz b
  have va : Commute v a := central_L1 (i+1) nil hv ha
  have vk : Commute v ⁅a,b⁆ := centralizes_commutator (i+1) nil hv _ _
  have equ : z*⁅a,b⁆*z⁻¹=⁅a,b⁆ := by
    rw [conjugate_commutatorElement]
    change ⁅MulAut.conj z a,MulAut.conj z b⁆ = _
    rw [conj_eq_commutatorElement_mul,conj_eq_commutatorElement_mul]
    change ⁅u*a,v*b⁆ = _
    rw [commutatorElement_mul_left_eq_conj_mul, (uc (v*b)).commutator_eq,mul_one,
      (uc _).eq,mul_inv_cancel_right,commutatorElement_mul_right_eq_mul_conj,
      va.symm.commutator_eq,one_mul,vk.eq,mul_inv_cancel_right]
  exact mul_inv_eq_iff_eq_mul.mp equ

theorem central_L2 (i : ℕ) (nil : L G (i+3)=⊥) {z a : G} (hz : z ∈ L G i) (ha : a ∈ L G 2) :
    Commute z a := by
  have L : L G 2 ≤ Subgroup.centralizer {z} := by
    change ⁅L G 1,(⊤ : Subgroup G)⁆ ≤ _
    exact Subgroup.commutator_le.mpr fun p hp q _ =>
      Subgroup.mem_centralizer_singleton_iff.mpr (central_gen_L2 i nil hz hp q).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (L ha)).symm

end HaarClass6Commute
#print axioms HaarClass6Commute.central_L2
