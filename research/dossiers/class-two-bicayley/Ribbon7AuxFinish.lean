import Ribbon7AuxLayers
import Ribbon7AuxCollect

namespace Ribbon7Aux
open HaarUniversal36 HaarClass4Structure
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

private theorem cent2 (f : G →* (G ⧸ L G 2)) (hf : f = QuotientGroup.mk' (L G 2))
    (a b d : G) : Commute ⁅f a,f b⁆ (f d) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement,← map_commutatorElement,hf]
  exact (QuotientGroup.eq_one_iff _).mpr (next (next (Subgroup.mem_top a) b) d)

theorem h_layer (x y : G) : h x y ∈ L G 2 := by
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
  exact hl

theorem r_layer (x y : G) : res x y∈L G 4 := res_layer_of x y (h_layer x y)

theorem z_layer (x y : G) : Ribbon5Law.trace x y false wc∈L G 6 := z_layer_of x y (h_layer x y)

theorem z_central (nil : L G 7=⊥) (x y g : G) :
    Commute (Ribbon5Law.trace x y false wc) g := by
  apply commutatorElement_eq_one_iff_commute.mp
  have E := next (z_layer x y) g
  rwa [show 6+1=7 from rfl,nil,Subgroup.mem_bot] at E

private theorem map_h (f : G→*H) (x y : G) :
    f (h x y)=h (f x) (f y) := by simp [h,q,map_commutatorElement]

private theorem map_delta (f : G→*H) (x y : G) :
    f (delta x y)=delta (f x) (f y) := by simp [delta]

theorem exceptional_proj (x y : G) (i j : Nat)
    (I : (i=48 ∧ j=98) ∨ (i=49 ∧ j=99) ∨ (i=50 ∧ j=100)) :
    let f := QuotientGroup.mk' (L G 3)
    f (diff x y i j) = (f (h x y))⁻¹ := by
  dsimp only
  let f := QuotientGroup.mk' (L G 3)
  have n : L (G ⧸ L G 3) 3=⊥ := quotient_nil (G:=G) 3
  have E : f (delta x y)=(f (h x y))⁻¹ := by
    rw [map_delta,map_h,delta_eq_inv _ _ n]
  rcases I with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rw [diff48]
    exact E
  · rw [diff49]
    exact E
  · change f (diff x y 50 100)=(f (h x y))⁻¹
    rw [diff50,map_mul,map_mul,map_inv,E]
    have C : Commute (f (h x y)) (f x) := by
      rw [map_h]
      exact h_central_class3 _ _ n _
    rw [C.inv_left.inv_right.symm.eq,mul_assoc,inv_mul_cancel,mul_one]

theorem exceptional_ne (nil : L G 7=⊥) (x y : G)
    (Z : Ribbon5Law.trace x y false wc≠1) (i j : Nat)
    (I : (i=48 ∧ j=98) ∨ (i=49 ∧ j=99) ∨ (i=50 ∧ j=100)) :
    diff x y i j≠1 := by
  intro H
  have E := exceptional_proj x y i j I
  dsimp only at E
  rw [H,map_one] at E
  have M : h x y∈L G 3 := (QuotientGroup.eq_one_iff _).mp (inv_eq_one.mp E.symm)
  exact Z (z_one_of_h_deep nil x y M)

end Ribbon7Aux
#print axioms Ribbon7Aux.z_central
#print axioms Ribbon7Aux.exceptional_ne
