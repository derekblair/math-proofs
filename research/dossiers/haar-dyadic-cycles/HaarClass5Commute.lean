import HaarUniversal36

namespace HaarClass5Commute
open HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem centralizes_commutator (i : ℕ) (nil : L G (i+1+1)=⊥) {z : G}
    (hz : z ∈ L G i) (a b : G) : Commute z ⁅a,b⁆ := by
  have hc (v w : G) : Commute ⁅z,v⁆ w := by
    apply commutatorElement_eq_one_iff_commute.mp
    have hh := next (next hz v) w
    rw [nil] at hh
    exact Subgroup.mem_bot.mp hh
  have h : z * ⁅a,b⁆ * z⁻¹ = ⁅a,b⁆ := by
    rw [conjugate_commutatorElement]
    change ⁅MulAut.conj z a,MulAut.conj z b⁆ = _
    rw [conj_eq_commutatorElement_mul,conj_eq_commutatorElement_mul]
    exact strip a b _ _ (hc a) (hc b)
  exact mul_inv_eq_iff_eq_mul.mp h

theorem comm_delta {z : G} (hz : z ∈ L G 2) (a b : G) :
    ⁅z,⁅a,b⁆⁆ ∈ L G 4 := by
  let Q := L G 4
  let f := QuotientGroup.mk' Q
  have hm (i : ℕ) : (L G i).map f = L (G ⧸ Q) i := by
    rw [Subgroup.map_lowerCentralSeries,
        Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective Q)]
  have nil : L (G ⧸ Q) 4 = ⊥ := by
    rw [← hm 4,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have hz' : f z ∈ L (G ⧸ Q) 2 := hm 2 ▸ Subgroup.mem_map_of_mem f hz
  have cc := centralizes_commutator 2 nil hz' (f a) (f b)
  apply (QuotientGroup.eq_one_iff (N:=Q) _).mp
  change f ⁅z,⁅a,b⁆⁆ = 1
  rw [map_commutatorElement,map_commutatorElement,cc.commutator_eq]

theorem centralizes_triple (nil : L G 5=⊥) {z : G} (hz : z ∈ L G 2) (a b c : G) :
    Commute z ⁅⁅a,b⁆,c⁆ := by
  let D := ⁅a,b⁆
  let u := ⁅z,D⁆
  let v := ⁅z,c⁆
  have uc (w : G) : Commute u w := by
    apply commutatorElement_eq_one_iff_commute.mp
    have h := next (comm_delta hz a b) w
    change ⁅u,w⁆ ∈ L G 5 at h
    rw [nil] at h
    exact Subgroup.mem_bot.mp h
  have hv : v ∈ L G 3 := next hz c
  have vD : Commute v D := centralizes_commutator 3 nil hv a b
  have vK : Commute v ⁅D,c⁆ := centralizes_commutator 3 nil hv D c
  have equ : z * ⁅D,c⁆ * z⁻¹ = ⁅D,c⁆ := by
    rw [conjugate_commutatorElement]
    change ⁅MulAut.conj z D,MulAut.conj z c⁆ = _
    rw [conj_eq_commutatorElement_mul,conj_eq_commutatorElement_mul]
    change ⁅u*D,v*c⁆ = _
    rw [commutatorElement_mul_left_eq_conj_mul, (uc (v*c)).commutator_eq,mul_one,
      (uc _).eq,mul_inv_cancel_right,commutatorElement_mul_right_eq_mul_conj,
      vD.symm.commutator_eq,one_mul,vK.eq,mul_inv_cancel_right]
  exact mul_inv_eq_iff_eq_mul.mp equ

theorem centralizes_conj_inverse_triple (nil : L G 5=⊥) {z : G} (hz : z ∈ L G 2)
    (a b c t : G) : Commute z (t * ⁅⁅a,b⁆,c⁆⁻¹ * t⁻¹) := by
  have hzi : t⁻¹*z*t ∈ L G 2 := by
    have ht := (inferInstance : (L G 2).Normal).conj_mem z hz t⁻¹
    simpa using ht
  have hc := (centralizes_triple nil hzi a b c).inv_right.eq
  change z * (t * ⁅⁅a,b⁆,c⁆⁻¹ * t⁻¹) = (t * ⁅⁅a,b⁆,c⁆⁻¹ * t⁻¹) * z
  calc
    _ = t * ((t⁻¹*z*t) * ⁅⁅a,b⁆,c⁆⁻¹) * t⁻¹ := by group
    _ = _ := by rw [hc]; group

end HaarClass5Commute
#print axioms HaarClass5Commute.centralizes_conj_inverse_triple
