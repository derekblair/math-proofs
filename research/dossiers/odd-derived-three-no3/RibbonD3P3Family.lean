import RibbonD3P3Use
import RibbonP3Odd
import RibbonIA

namespace RibbonD3P3
open RibbonDumbbell RibbonDerived3 HaarClass4Structure HaarClass4Generate HaarClass4Ports
open RibbonClass4Fallback
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem swap_c (x y : G) : portC y x=(portC x y)⁻¹ := by
  simp only [portC,commutatorElement_inv]

private theorem swap_u (nil : LS G 3=⊥) (x y : G) :
    portU y x=(portV x y)⁻¹ := by
  unfold portU
  rw [swap_c,commutatorElement_inv_left,←commutatorElement_inv]
  change (portC x y)⁻¹ * (portV x y)⁻¹ * portC x y=(portV x y)⁻¹
  have e := (RibbonP3.center_of_L2 nil (layer_v x y) (portC x y)⁻¹).symm.inv_right.eq
  rw [e,mul_assoc,inv_mul_cancel,mul_one]

/-- The pure projected-order-three branch: when the actual pair-generated
group has nontrivial third graded layer, no affine field shadow is needed. -/
theorem nonstable_projected_three (d3 : DLS G 3=⊥) (x y : G)
    (gen : Generates x y)
    (order : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=3)
    (nst : LS G 2 ≠ LS G 3) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 128 ∨ Ribbon.Cycle x y 256 := by
  let p := QuotientGroup.mk' (LS G 3)
  let F := QuotientGroup.mk' (LS G 2)
  have LSle : LS G 3 ≤ LS G 2 := Subgroup.lowerCentralSeries_antitone ⊤ (by decide : 2≤3)
  let f : (G ⧸ LS G 3) →* (G ⧸ LS G 2) :=
    QuotientGroup.lift _ F (by rwa [QuotientGroup.ker_mk'])
  have eval (g : G) : f (p g) = F g := rfl
  have nilH : LS (G ⧸ LS G 3) 3=⊥ := by
    rw [←map_ls p (QuotientGroup.mk'_surjective _) 3,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have gh := map_gen p (QuotientGroup.mk'_surjective _) gen
  have ker : f.ker = LS (G ⧸ LS G 3) 2 := by
    rw [←map_ls p (QuotientGroup.mk'_surjective _) 2]
    ext z
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (LS G 3) z
    constructor
    · intro h
      have h' : F g=1 := h
      exact Subgroup.mem_map_of_mem p ((QuotientGroup.eq_one_iff _).mp h')
    · rintro ⟨v,hv,e⟩
      change f (p g)=1
      rw [← e,eval]
      exact (QuotientGroup.eq_one_iff _).mpr hv
  have cMap (a b : G) : p (portC a b)=portC (p a) (p b) := by
    simp only [portC,map_commutatorElement,map_inv]
  have kills : ∀ z ∈ DLS G 1, p z=1 := by
    intro z hz
    apply (QuotientGroup.eq_one_iff _).mpr
    have h := RibbonIA.weight_pair (⊤ : Subgroup G) 1 1
    exact h hz
  have nz : LS (G ⧸ LS G 3) 2 ≠ ⊥ := by
    intro b
    rw [←map_ls p (QuotientGroup.mk'_surjective _) 2,Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at b
    exact nst (le_antisymm b LSle)
  by_cases u0 : portU (p x) (p y) = 1
  · have v0 : portV (p x) (p y) ≠ 1 := by
      intro hy
      apply nz
      rw [RibbonP3.L2_eq_two nilH _ _ gh,u0,hy]
      apply bot_unique
      apply (Subgroup.closure_le _).mpr
      intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl|rfl <;> exact Subgroup.one_mem _
    have n : portU (p y) (p x)≠1 := by
      rw [swap_u nilH]
      exact inv_ne_one.mpr v0
    have altGen : Generates (p y) (p x) := by
      unfold Generates at gh ⊢
      rwa [Set.pair_comm]
    have altO : orderOf (f (portC (p y) (p x)))=3 := by
      rw [swap_c,map_inv,orderOf_inv,←cMap,eval]
      exact order
    rcases local_visible d3 y x p f kills nilH altGen ker altO n with h|h|h
    · exact Or.inl (RibbonP3.flip_cycle h)
    · exact Or.inr (Or.inl (RibbonP3.flip_cycle h))
    · exact Or.inr (Or.inr (RibbonP3.flip_cycle h))
  · have O : orderOf (f (portC (p x) (p y)))=3 := by rw [←cMap,eval]; exact order
    exact local_visible d3 x y p f kills nilH gh ker O u0

#print axioms nonstable_projected_three
end RibbonD3P3
