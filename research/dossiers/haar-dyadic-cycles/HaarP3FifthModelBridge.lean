import HaarP3FifthData
import HaarP3FifthLaws
import HaarP3FifthCharacter

namespace HaarP3FifthModelBridge
open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarP3LayerGen HaarP3FifthData HaarP3Char
open HaarP3FifthCharacter HaarP3CollectActions HaarClass4CollectCore
variable {G : Type*} [Group G]

theorem cube_comm (u x a : G) (ax : ⁅u,x⁆=a)
    (ua : Commute u a) (h : Central (u^(3:ℕ))) : a^(3:ℕ)=1 := by
  let E := MulAut.conj x
  have cu : E (u^(3:ℕ))=u^(3:ℕ) := by
    change x*(u^(3:ℕ))*x⁻¹=_
    rw [(h x).symm.eq,mul_inv_cancel_right]
  have e := HaarP3FifthLaws.conj_of_right_comm x u a ax
  change E u=a⁻¹*u at e
  rw [map_pow,e,ua.symm.inv_left.mul_pow] at cu
  have r : (a⁻¹)^(3:ℕ)=1 := mul_right_cancel (cu.trans (one_mul _).symm)
  simpa only [inv_pow,inv_eq_one] using r

theorem central_map {H : Type*} [Group H] (φ : G→*H) (onto : Function.Surjective φ)
    {z : G} (h : Central z) : Central (φ z) := by
  intro w
  obtain ⟨q,rfl⟩ := onto w
  exact (h q).map φ

def makeModel (nil : LS G 5=⊥) (x y : G)
    (E : HaarP3Class4Dispatch.Exceptional x y)
    (cube : ∀ w∈LS G 4, w^(3:ℕ)=1)
    (χ : LS G 4 →* C3) (z : LS G 4) (hz : digit (χ z)=1) :
    let S := LS G 4
    let cent : S≤Subgroup.center G := ls4_center_of_class5 nil
    let N := centralKernel S χ
    letI : N.Normal := kernel_normal cent χ
    Model (G ⧸ N) := by
  let S := LS G 4
  let cent : S≤Subgroup.center G := ls4_center_of_class5 nil
  let N := centralKernel S χ
  let : N.Normal := kernel_normal cent χ
  let φ := QuotientGroup.mk' N
  let c := portC x y
  let u := portU x y
  let v := portV x y
  let a := ⁅u,x⁆
  let D := data x y E
  let p : S := ⟨⁅a,x⁆,next_layer (next_layer (layer_u x y) x) x⟩
  let q : S := ⟨⁅a,y⁆,next_layer (next_layer (layer_u x y) x) y⟩
  let t0 : S := ⟨v*u*a,D.h0⟩
  let t1 : S := ⟨u^(3:ℕ),D.h1⟩
  let t2 : S := ⟨⁅u,y⁆*a,D.h2⟩
  let P := parameters χ p q t0 t1 t2
  have aL : a∈LS G 3 := next_layer (layer_u x y) x
  have ca : Commute c a :=
    (HaarClass5Commute.centralizes_commutator 3 nil aL x⁻¹ y⁻¹).symm
  have ua : Commute u a := HaarClass5L2Abelian.l2_comm nil (layer_u x y)
    (Subgroup.lowerCentralSeries_antitone _ (by decide : 2≤3) aL)
  have cz : Central z.val := fun w => (Subgroup.mem_center_iff.mp (cent z.property) w).symm
  have ct : Central (u^(3:ℕ)) := fun w => (Subgroup.mem_center_iff.mp (cent D.h1) w).symm
  have a3 := cube_comm u x a rfl ua ct
  have z3 := cube z.val z.property
  refine HaarP3FifthLaws.modelOf (φ x) (φ y) (φ c) (φ u) (φ a) (φ z.val) P
    ?_ (central_map φ (QuotientGroup.mk'_surjective N) cz) (ca.map φ) (ua.map φ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have e := congrArg φ (ports_xy x y); simpa only [map_mul] using e
  · exact (map_commutatorElement φ c x).symm
  · rw [←map_commutatorElement,←map_mul,←map_mul]
    exact mapped_power cent χ z t0 hz
  · exact (map_commutatorElement φ u x).symm
  · rw [←map_commutatorElement,←map_mul]
    exact mapped_power cent χ z t2 hz
  · rw [←map_commutatorElement]
    exact mapped_power cent χ z p hz
  · rw [←map_commutatorElement]
    exact mapped_power cent χ z q hz
  · change (φ u)^((3:ℕ):ℤ)=_
    rw [zpow_natCast,←map_pow]
    exact mapped_power cent χ z t1 hz
  · change (φ a)^((3:ℕ):ℤ)=_
    rw [zpow_natCast,←map_pow,a3,map_one]
  · change (φ z.val)^((3:ℕ):ℤ)=_
    rw [zpow_natCast,←map_pow,z3,map_one]

end HaarP3FifthModelBridge
#print axioms HaarP3FifthModelBridge.makeModel
