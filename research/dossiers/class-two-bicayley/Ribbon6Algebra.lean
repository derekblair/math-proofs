import Ribbon6Chart

namespace Ribbon6
open HaarUniversal36 HaarClass5Commute Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem cent2 (f : G →* (G ⧸ L G 2)) (hf : f = QuotientGroup.mk' (L G 2))
    (a b d : G) : Commute ⁅f a,f b⁆ (f d) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement,← map_commutatorElement,hf]
  exact (QuotientGroup.eq_one_iff _).mpr (next (next (Subgroup.mem_top a) b) d)

theorem residue_layer (x y : G) : residue x y ∈ L G 4 := by
  let q := ⁅x,y⁻¹⁆
  let g := x⁻¹*⁅y,x^2⁆*x
  let h := g*q⁻¹*q⁻¹
  let f := QuotientGroup.mk' (L G 2)
  have C : ∀ a b d : G, Commute ⁅f a,f b⁆ (f d) := cent2 f rfl
  have E : f g=(f q)^2 := by
    have p := C y x y
    have e := C y x x
    simp only [g,q,map_mul,map_inv,map_pow,map_commutatorElement]
    have J : ⁅f x,(f y)⁻¹⁆ = ⁅f y,f x⁆ := by
      rw [commutatorElement_inv_right,p.symm.inv_left.eq]
      group
    have K : ⁅f y,(f x)^2⁆ = ⁅f y,f x⁆^2 := by
      rw [pow_two,commutatorElement_mul_right_eq_mul_conj]
      calc
        _ = ⁅f y,f x⁆ * (f x*⁅f y,f x⁆) * (f x)⁻¹ := by group
        _ = _ := by rw [e.symm.eq,pow_two]; group
    rw [J,K,(e.pow_left 2).symm.inv_left.eq]
    group
  have hl : h∈L G 2 := by
    apply (QuotientGroup.eq_one_iff _).mp
    change f h=1
    simp only [h,map_mul,map_inv,E,pow_two]
    group
  have ge : g = h*q^2 := by simp only [h,pow_two]; group
  have K : ⁅q,g⁆ = ⁅q,h⁆ := by
    rw [ge,commutatorElement_mul_right_eq_mul_conj,
      ((Commute.refl q).pow_right 2).commutator_eq,mul_one,mul_inv_cancel_right]
  have J : ⁅q,h⁆∈L G 4 := by
    rw [←commutatorElement_inv]
    exact (L G 4).inv_mem (comm_delta hl x y⁻¹)
  rw [explicit]
  exact (inferInstance : (L G 4).Normal).conj_mem _ (K ▸ J) _

theorem upper_U (x y : G) : U x y ∈ L G 1 := by
  change U x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one, ← Abelianization.ker_of]
  change Abelianization.of (U x y)=1
  simp only [U,map_mul,map_inv]
  let X := Abelianization.of x
  let Y := Abelianization.of y
  change Y⁻¹*X*X*Y⁻¹*X⁻¹*Y*X⁻¹*Y=1
  calc
    _ = (X*X*X⁻¹*X⁻¹)*(Y⁻¹*Y⁻¹*Y*Y) := by ac_rfl
    _ = 1 := by group

theorem residue_commute (nil : L G 6=⊥) (x y : G) : Commute (residue x y) (U x y) := by
  have le : L G 1 ≤ Subgroup.centralizer ({residue x y}:Set G) := by
    change ⁅(⊤:Subgroup G),(⊤:Subgroup G)⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (centralizes_commutator 4 nil (residue_layer x y) a b).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (le (upper_U x y))).symm

theorem close (nil : L G 6=⊥) (x y : G) : pathAt x y wc 64 = pathAt x y wc 0 := by
  have E : U x y*V x y = V x y*U x y := by
    have H := (residue_commute nil x y).eq
    change U x y*V x y*U x y=U x y*(U x y*V x y) at H
    exact (mul_left_cancel (by simpa only [mul_assoc] using H)).symm
  rw [c_end,E,mul_inv_cancel]
  rfl

end Ribbon6
#print axioms Ribbon6.residue_layer
#print axioms Ribbon6.close
