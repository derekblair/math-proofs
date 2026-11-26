import RibbonDerived3Algebra

namespace RibbonD3Closure
open RibbonDerived3
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The first balanced rotation has endpoint displacement in γ₃(D). -/
theorem rotateResidue_mem {r u : G} (hr : r ∈ DLS G 1) (hu : u ∈ Derived G) :
    r * u⁻¹ * r⁻¹ * u ∈ DLS G 2 := by
  have H : ⁅r,u⁻¹⁆ ∈ DLS G 2 := by
    change _ ∈ ⁅DLS G 1, Derived G⁆
    exact Subgroup.commutator_mem_commutator hr ((Derived G).inv_mem hu)
  simpa only [commutatorElement_def, inv_inv] using H

/-- A further balanced rotation of that residue closes in derived class at most three. -/
theorem rotateTwice_close (d3 : DLS G 3 = ⊥) {r u p : G}
    (hr : r ∈ DLS G 1) (hu : u ∈ Derived G) (hp : p ∈ Derived G) :
    let z := r * u⁻¹ * r⁻¹ * u
    z * p⁻¹ * z⁻¹ * p = 1 := by
  dsimp
  have H : ⁅r * u⁻¹ * r⁻¹ * u,p⁻¹⁆ ∈ DLS G 3 := by
    change _ ∈ ⁅DLS G 2, Derived G⁆
    exact Subgroup.commutator_mem_commutator (rotateResidue_mem hr hu) ((Derived G).inv_mem hp)
  rw [d3] at H
  simpa only [commutatorElement_def, inv_inv] using Subgroup.mem_bot.mp H

/-- A nontrivial first residue forces the A residue nontrivial even modulo γ₃(D). -/
theorem base_nontrivial_mod_third (d3 : DLS G 3 = ⊥) {r u : G}
    (hu : u ∈ Derived G) (hne : r * u⁻¹ * r⁻¹ * u ≠ 1) : r ∉ DLS G 2 := by
  intro h
  apply hne
  have H : ⁅r,u⁻¹⁆ ∈ DLS G 3 := by
    change _ ∈ ⁅DLS G 2, Derived G⁆
    exact Subgroup.commutator_mem_commutator h ((Derived G).inv_mem hu)
  rw [d3] at H
  simpa only [commutatorElement_def, inv_inv] using Subgroup.mem_bot.mp H

#print axioms rotateTwice_close
#print axioms base_nontrivial_mod_third
end RibbonD3Closure
