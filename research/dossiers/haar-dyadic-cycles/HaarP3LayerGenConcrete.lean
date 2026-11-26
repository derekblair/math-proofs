import HaarP3LayerGenExpo

namespace HaarP3LayerGen

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate
variable {G : Type*} [Group G]

theorem fifth_layer_exceptional (nil : LS G 5=⊥) (x y : G) (gen : Generates x y)
    (rel : let φ := QuotientGroup.mk' (LS G 4)
           let e := make (ls4quot_class4 G) (φ x) (φ y)
           e.v=e.u^(2:ℕ)*e.a^(2:ℕ) ∧ e.u^(3:ℕ)=1 ∧ e.a^(3:ℕ)=1) :
    let A := ⁅portU x y,x⁆
    LS G 4 = Subgroup.closure ({⁅A,x⁆,⁅A,y⁆} : Set G) ∧
    ∀ w∈LS G 4, w^(3:ℕ)=1 := by
  let Q := G ⧸ LS G 4
  let φ := QuotientGroup.mk' (LS G 4)
  let h := ls4quot_class4 G
  let e := make h (φ x) (φ y)
  let A := ⁅portU x y,x⁆
  change e.v=e.u^(2:ℕ)*e.a^(2:ℕ) ∧ e.u^(3:ℕ)=1 ∧ e.a^(3:ℕ)=1 at rel
  have fA : φ A=e.a := by
    change φ ⁅portU x y,x⁆=⁅portU (φ x) (φ y),φ x⁆
    simp only [portU,portC,map_commutatorElement,map_inv]
  have hA : A∈LS G 3 := next_layer (layer_u x y) x
  have hAc : A^3∈LS G 4 := (QuotientGroup.eq_one_iff _).mp (by
    change φ (A^3)=1
    rw [map_pow,fA]
    exact rel.2.2)
  have hUc : e.u^(3:ℕ)∈LS Q 3 := by rw [rel.2.1]; exact Subgroup.one_mem _
  have hAt : e.a^(2:ℕ)∈LS Q 3 := Subgroup.pow_mem _ (tail_layers h (φ x) (φ y)).1 _
  have ⟨_,hb,hd⟩ := pivotU h (φ x) (φ y) 2 hUc _ hAt rel.1
  have onto := QuotientGroup.mk'_surjective (LS G 4)
  have span : (LS G 3).map φ=Subgroup.zpowers (φ A) := by
    rw [fA,map_ls φ onto]
    exact spanU h _ _ (map_gen φ onto gen) 2 hb hd
  exact ⟨ls4_eq_two_closure nil x y A gen hA span, fifth_all_cubes nil x y A gen hA hAc span⟩

end HaarP3LayerGen

#print axioms HaarP3LayerGen.fifth_layer_exceptional
