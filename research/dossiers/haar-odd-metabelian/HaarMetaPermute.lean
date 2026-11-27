import HaarAnyPorts
import HaarClass4Generate
import HaarMetaShortRelations
import Mathlib.Algebra.Group.TypeTags.Basic

namespace HaarMetaPermute

open HaarAllNoncommuting

variable {G : Type*} [Group G]

/-- The three group-valued ports in their original order. -/
def ports (x y : G) (i : Fin 3) : G := ![1,x,y] i

private theorem label_iff (p : Fin 3 → G) (u v : G) :
    (u = v * p 0 ∨ u = v * p 1 ∨ u = v * p 2) ↔
      ∃ i, u = v * p i := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨i,h⟩
    fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

private theorem label_perm (p : Fin 3 → G) (σ : Equiv.Perm (Fin 3)) (u v : G) :
    (u = v * p (σ 0) ∨ u = v * p (σ 1) ∨ u = v * p (σ 2)) ↔
      (u = v * p 0 ∨ u = v * p 1 ∨ u = v * p 2) := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (label_iff (p ∘ σ) u v).mp h
    exact (label_iff p u v).mpr ⟨σ i,hi⟩
  · intro h
    obtain ⟨i, hi⟩ := (label_iff p u v).mp h
    exact (label_iff (p ∘ σ) u v).mpr ⟨σ.symm i, by
      change u = v * p (σ (σ.symm i))
      simpa using hi⟩

theorem adj_perm (p : Fin 3 → G) (σ : Equiv.Perm (Fin 3)) (a b : Bool × G) :
    HaarAnyPorts.adj (p (σ 0)) (p (σ 1)) (p (σ 2)) a b ↔
      HaarAnyPorts.adj (p 0) (p 1) (p 2) a b := by
  simp only [HaarAnyPorts.adj, label_perm p σ]

theorem portCycle_perm (p : Fin 3 → G) (σ : Equiv.Perm (Fin 3)) (k : ℕ) :
    HaarAnyPorts.HasPortCycle (p (σ 0)) (p (σ 1)) (p (σ 2)) k ↔
      HaarAnyPorts.HasPortCycle (p 0) (p 1) (p 2) k := by
  simp only [HaarAnyPorts.HasPortCycle, adj_perm p σ]

theorem portCycle_one (x y : G) (k : ℕ) :
    HaarAnyPorts.HasPortCycle 1 x y k ↔ HasCycle x y k := by
  simp only [HaarAnyPorts.HasPortCycle, HasCycle, HaarAnyPorts.adj, HaarCycle.haarAdj, mul_one]

/-- A cycle on any permuted and right-normalized port triple transfers back to the
original Haar graph, with the number of vertices and their distinctness preserved. -/
theorem normalizedCycle (x y : G) (σ : Equiv.Perm (Fin 3)) {k : ℕ}
    (h : HasCycle (ports x y (σ 1) * (ports x y (σ 0))⁻¹)
      (ports x y (σ 2) * (ports x y (σ 0))⁻¹) k) : HasCycle x y k := by
  have hp := HaarAnyPorts.map_cycle _ _ _ h
  have hq := (portCycle_perm (ports x y) σ k).mp hp
  exact (portCycle_one x y k).mp (by simpa [ports] using hq)

theorem ports_injective (x y : G) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) :
    Function.Injective (ports x y) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports, Ne.symm hx, Ne.symm hy, Ne.symm hxy]

theorem normalized_distinct (x y : G) (σ : Equiv.Perm (Fin 3))
    (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) :
    ports x y (σ 1) * (ports x y (σ 0))⁻¹ ≠ 1 ∧
    ports x y (σ 2) * (ports x y (σ 0))⁻¹ ≠ 1 ∧
    ports x y (σ 1) * (ports x y (σ 0))⁻¹ ≠
      ports x y (σ 2) * (ports x y (σ 0))⁻¹ := by
  apply HaarAnyPorts.as_three
  all_goals
    intro he
    have he' := σ.injective (ports_injective x y hx hy hxy he)
    exact (by decide : ¬_) he'

/-- Changing the distinguished port and relabeling does not affect generation. -/
theorem normalized_generates (x y : G) (σ : Equiv.Perm (Fin 3))
    (hg : HaarClass4Generate.Generates x y) :
    HaarClass4Generate.Generates
      (ports x y (σ 1) * (ports x y (σ 0))⁻¹)
      (ports x y (σ 2) * (ports x y (σ 0))⁻¹) := by
  let p := ports x y
  let r := p (σ 0)
  let X := p (σ 1) * r⁻¹
  let Y := p (σ 2) * r⁻¹
  let S := Subgroup.closure ({X,Y} : Set G)
  change S = ⊤
  have hport (q : Fin 3) : p q * r⁻¹ ∈ S := by
    obtain ⟨i, rfl⟩ := σ.surjective q
    fin_cases i
    · change r * r⁻¹ ∈ S
      simp
    · exact Subgroup.subset_closure (by simp : X ∈ ({X,Y} : Set G))
    · exact Subgroup.subset_closure (by simp : Y ∈ ({X,Y} : Set G))
  have hri : r⁻¹ ∈ S := by simpa [p,ports] using hport 0
  have hr : r ∈ S := by simpa using S.inv_mem hri
  have hplain (q : Fin 3) : p q ∈ S := by
    simpa [mul_assoc] using S.mul_mem (hport q) hr
  have incl : Subgroup.closure ({x,y} : Set G) ≤ S := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa [p,ports] using hplain 1
    · simpa [p,ports] using hplain 2
  change Subgroup.closure ({x,y} : Set G) = ⊤ at hg
  rw [hg] at incl
  exact top_unique incl

variable {Q : Type*} [CommGroup Q]

/-- Express a group homomorphism to a commutative group in additive notation. -/
def image (f : G →* Q) (g : G) : Additive Q := Additive.ofMul (f g)

theorem image_normalized (f : G →* Q) (s r : G) :
    image f (s * r⁻¹) = image f s - image f r := by
  simp [image, sub_eq_add_neg]

private theorem image_port (f : G →* Q) (x y : G) (i : Fin 3) :
    image f (ports x y i) = HaarMetaShortRelations.ports (image f x) (image f y) i := by
  fin_cases i <;> simp [ports, HaarMetaShortRelations.ports, image]

/-- For a short relation among the quotient images, pick distinct normalized actual
ports realizing its normal form. Every cycle on these ports transfers to the original. -/
theorem normalize (f : G →* Q) (x y : G) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (h₂ : ∀ z : Additive Q, (2 : ℤ) • z = 0 → z = 0)
    (i j : ℤ) (hi : -3 ≤ i ∧ i ≤ 3) (hj : -3 ≤ j ∧ j ≤ 3)
    (hn : i ≠ 0 ∨ j ≠ 0) (h : i • image f x + j • image f y = 0) :
    ∃ σ : Equiv.Perm (Fin 3),
      let X := ports x y (σ 1) * (ports x y (σ 0))⁻¹
      let Y := ports x y (σ 2) * (ports x y (σ 0))⁻¹
      HaarMetaShortRelations.NormalForm (image f X) (image f Y) ∧
      (X ≠ 1 ∧ Y ≠ 1 ∧ X ≠ Y) ∧ (∀ k, HasCycle X Y k → HasCycle x y k) := by
  obtain ⟨σ, hσ⟩ := HaarMetaShortRelations.normalize (image f x) (image f y) h₂ i j hi hj hn h
  refine ⟨σ, ?_, normalized_distinct x y σ hx hy hxy, fun _ => normalizedCycle x y σ⟩
  simpa only [image_normalized, image_port] using hσ

end HaarMetaPermute

#print axioms HaarMetaPermute.normalize
#print axioms HaarMetaPermute.normalized_generates
