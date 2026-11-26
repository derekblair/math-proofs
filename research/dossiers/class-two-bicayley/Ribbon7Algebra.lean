import Ribbon7Chart
import Ribbon7Layers
import Ribbon7AuxFinish

namespace Ribbon7
open Ribbon5Bridge HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem U_layer (x y : G) : U x y∈L G 1 := by
  change U x y ∈ (⊤:Subgroup G).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one,← Abelianization.ker_of]
  change Abelianization.of (U x y)=1
  simp only [U,map_mul,map_inv]
  let a := Abelianization.of x
  let b := Abelianization.of y
  change a⁻¹*b⁻¹*a*a*b⁻¹*a⁻¹*b*a⁻¹*b*a=1
  calc
    _ = (a⁻¹*a*a*a⁻¹*a⁻¹*a)*(b⁻¹*b⁻¹*b*b) := by ac_rfl
    _ = 1 := by group

theorem R_layer (x y : G) : R x y ∈ L G 4 :=
  Ribbon7Aux.r_layer x y

theorem zconj (x y : G) :
    Z x y = (U x y)⁻¹ * ⁅U x y, R x y⁆ * U x y := by
  simp only [Z,R,commutatorElement_def]
  group

theorem Z_layer (x y : G) : Z x y ∈ L G 6 := by
  have E : ⁅U x y,R x y⁆ ∈ L G 6 := by
    rw [← commutatorElement_inv]
    exact (L G 6).inv_mem (comm_mem 4 (R_layer x y) (U_layer x y))
  rw [zconj]
  simpa only [inv_inv] using (inferInstance : (L G 6).Normal).conj_mem _ E (U x y)⁻¹

theorem nz_R (x y : G) (h : Z x y≠1) : R x y≠1 := by
  intro E
  apply h
  rw [zconj,E,commutatorElement_one_right,mul_one,inv_mul_cancel]

theorem nz_mix (nil : L G 7=⊥) (x y : G) (h : Z x y≠1) : (R x y)⁻¹*Z x y≠1 := by
  intro E
  have H : Z x y=R x y := by
    apply mul_left_cancel (a:=(R x y)⁻¹)
    rw [E,inv_mul_cancel]
  apply h
  have C : Commute (U x y) (R x y) := H ▸ (last_central 6 nil (Z_layer x y) (U x y)).symm
  rw [zconj,C.commutator_eq,mul_one,inv_mul_cancel]

theorem close128 (nil : L G 7=⊥) (x y : G) : pathAt x y wt 128=pathAt x y wt 0 := by
  rw [t_end]
  have H := (last_central 6 nil (Z_layer x y) (K x y)).inv_right
  rw [H.eq]
  apply Prod.ext
  · rfl
  · simp only [pathAt,run,start,List.take_zero,List.foldl_nil]
    group

end Ribbon7
#print axioms Ribbon7.Z_layer
#print axioms Ribbon7.close128
