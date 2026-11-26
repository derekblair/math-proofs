import RibbonMetaDrop
import Ribbon6P3Local

namespace RibbonDerivedTwo
open HaarClass4Structure HaarClass4Ports Ribbon5Bridge Ribbon6
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The commutator subgroup has nilpotency class at most two. -/
def D2 (G : Type*) [Group G] : Prop :=
  ∀ a ∈ LS G 1, ∀ b ∈ LS G 1, ∀ z ∈ LS G 1, Commute ⁅a,b⁆ z

theorem of_derived_class2 (nil : LS (LS G 1) 2=⊥) : D2 G := by
  intro a ha b hb z hz
  let A : LS G 1 := ⟨a,ha⟩
  let B : LS G 1 := ⟨b,hb⟩
  let Z : LS G 1 := ⟨z,hz⟩
  have h := next_layer (n:=1) (next_layer (n:=0) (Subgroup.mem_top A) B) Z
  rw [nil,Subgroup.mem_bot] at h
  apply commutatorElement_eq_one_iff_commute.mp
  exact congrArg Subtype.val h

theorem subgroup_d2 (m : D2 G) (S : Subgroup G) : D2 S := by
  intro a ha b hb z hz
  have incl : (LS S 1).map S.subtype ≤ LS G 1 := by
    rw [Subgroup.top_subtype_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono 1 (show S≤⊤ from le_top)
  have h := m a.val (incl (Subgroup.mem_map_of_mem _ ha)) b.val
    (incl (Subgroup.mem_map_of_mem _ hb)) z.val
    (incl (Subgroup.mem_map_of_mem _ hz))
  exact Subtype.ext h.eq

theorem residue_commute (m : D2 G) (x y : G) : Commute (Ribbon6.residue x y) (U x y) := by
  let N : (LS G 1).Normal := inferInstance
  let q := ⁅x,y⁻¹⁆
  let g := x⁻¹*⁅y,x^2⁆*x
  let s := y⁻¹*x
  have A : q ∈ LS G 1 := next_layer (Subgroup.mem_top x) y⁻¹
  have B : ⁅y,x^2⁆ ∈ LS G 1 := next_layer (Subgroup.mem_top y) (x^2)
  have C : g ∈ LS G 1 := by simpa only [g,inv_inv] using N.conj_mem _ B x⁻¹
  rw [explicit,conjugate_commutatorElement]
  exact m (s*q*s⁻¹) (N.conj_mem _ A s) (s*g*s⁻¹) (N.conj_mem _ C s) _
    (upper_U x y)

theorem close (m : D2 G) (x y : G) : pathAt x y wc 64=pathAt x y wc 0 := by
  have E : U x y*V x y = V x y*U x y := by
    have H := (residue_commute m x y).eq
    change U x y*V x y*U x y=U x y*(U x y*V x y) at H
    exact (mul_left_cancel (by simpa only [mul_assoc] using H)).symm
  rw [c_end,E,mul_inv_cancel]
  rfl

end RibbonDerivedTwo
#print axioms RibbonDerivedTwo.of_derived_class2
#print axioms RibbonDerivedTwo.close
