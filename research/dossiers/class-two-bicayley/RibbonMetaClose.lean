import Ribbon6P3Chart
import Ribbon6Invert

namespace RibbonMeta
open Ribbon5Bridge HaarClass4Structure HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Metabelian in the literal sense: elements of the derived subgroup commute. -/
def Meta (G : Type*) [Group G] : Prop :=
  ∀ a ∈ LS G 1, ∀ b ∈ LS G 1, Commute a b

theorem residue_zero (m : Meta G) (x y : G) : Ribbon6.residue x y=1 := by
  rw [Ribbon6.explicit]
  have A : ⁅x,y⁻¹⁆ ∈ LS G 1 := next_layer (Subgroup.mem_top x) y⁻¹
  have B : ⁅y,x^2⁆ ∈ LS G 1 := next_layer (Subgroup.mem_top y) (x^2)
  have C : x⁻¹*⁅y,x^2⁆*x ∈ LS G 1 := by
    simpa only [inv_inv] using (inferInstance : (LS G 1).Normal).conj_mem _ B x⁻¹
  rw [(m _ A _ C).commutator_eq,mul_one,mul_inv_cancel]

theorem low_cycle (m : Meta G) (x y : G)
    (good : ∀ k : Nat, 1 ≤ k → k ≤ 4 →
      (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1) :
    Ribbon.Cycle x y 32 := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C, portU,map_commutatorElement] using U
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C, portV,map_commutatorElement] using V
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  let F : Bool×G → Bool × (G ⧸ LS G 2) := fun u => (u.1,f u.2)
  apply cycle_from_at x y Ribbon6.wa (by decide) (by rw [Ribbon6.a_end,residue_zero m]; rfl)
  have tr := transported f x y Ribbon6.wa Ribbon6.ta C cx cy xy (by decide +kernel)
    (fun i hi => Ribbon6.astep ⟨i,hi⟩)
  intro i j le E
  have e : vert (f x) (f y) C Ribbon6.ta[i.val]! = vert (f x) (f y) C Ribbon6.ta[j.val]! :=
    (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
  exact separates_low (f x) (f y) C cx cy xy good _ _ (Ribbon6.achart i j le) e

open Ribbon6 in
theorem cycle_of_good_table (m : Meta G) (x y : G) (q t : Fin 3) (h : OK q t)
    (key : ∀ i j : Fin 64, pathAt x y wc i.val = pathAt x y wc j.val →
      pkey q t i = pkey q t j) : Ribbon.Cycle x y 32 := by
  have prepend32 (i : Nat) (hi : i≤32) : pathAt x y wa i = pathAt x y wc i := by
    have E : wa.toList = wc.toList.take 32 := by decide +kernel
    simp only [pathAt,E,List.take_take,Nat.min_eq_left hi]
  apply cycle_from_at x y wa (by decide) (by rw [a_end,residue_zero m]; rfl)
  intro i j l E
  let I : Fin 64 := ⟨i.val,by omega⟩
  let J : Fin 64 := ⟨j.val,by omega⟩
  have ei : pathAt x y wa i.val = pathAt x y wc I.val := prepend32 _ i.isLt.le
  have ej : pathAt x y wa j.val = pathAt x y wc J.val := prepend32 _ j.isLt.le
  have z := p3chart q t h I J l (key I J (ei.symm.trans (E.trans ej)))
  change same i.val j.val at z
  unfold same at z
  omega

open Ribbon6 in
theorem cycle_of_tables (m : Meta G) (x y : G) (q t : Fin 3)
    (keyA : ∀ i j : Fin 64, pathAt x y wc i.val = pathAt x y wc j.val →
      pkey q t i = pkey q t j)
    (keyB : ∀ i j : Fin 64, pathAt x⁻¹ y wc i.val = pathAt x⁻¹ y wc j.val →
      pkey (-q) (-t) i = pkey (-q) (-t) j) : Ribbon.Cycle x y 32 := by
  rcases p3case q t with g|g
  · exact RibbonMeta.cycle_of_good_table m x y q t g keyA
  · exact (cycle_inv_left x y).mp (RibbonMeta.cycle_of_good_table m x⁻¹ y (-q) (-t) g keyB)

end RibbonMeta
#print axioms RibbonMeta.residue_zero
#print axioms RibbonMeta.low_cycle
#print axioms RibbonMeta.cycle_of_tables
