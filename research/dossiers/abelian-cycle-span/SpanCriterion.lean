import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace AbelianCycleChart

variable {M W : Type*} [AddCommGroup M] [DecidableEq M] [DecidableEq W]

def bad (rows : Finset W) (close : W → M) (clash : W → Finset M)
    (P : Submodule ℤ M) : Prop :=
  ∀ w ∈ rows, close w ∈ P → ∃ x ∈ clash w, x ∈ P

def candidates (rows : Finset W) (clash : W → Finset M) : Finset M := rows.biUnion clash

omit [DecidableEq W] in
theorem finite_span_criterion (rows : Finset W) (close : W → M) (clash : W → Finset M) :
    (∃ P : Submodule ℤ M, bad rows close clash P) ↔
      ∃ R : Finset M, R ⊆ candidates rows clash ∧
        bad rows close clash (Submodule.span ℤ (R : Set M)) := by
  constructor
  · rintro ⟨P,H⟩
    classical
    let T := candidates rows clash
    let R := T.filter (fun x => x ∈ P)
    have le : Submodule.span ℤ (R : Set M) ≤ P := by
      apply Submodule.span_le.mpr
      intro x hout
      exact (Finset.mem_filter.mp hout).2
    refine ⟨R,Finset.filter_subset _ _,?_⟩
    intro w hw hclose
    obtain ⟨x,hx,hP⟩ := H w hw (le hclose)
    have hT : x∈T := Finset.mem_biUnion.mpr ⟨w,hw,hx⟩
    have hR : x∈R := Finset.mem_filter.mpr ⟨hT,hP⟩
    exact ⟨x,hx,Submodule.subset_span hR⟩
  · rintro ⟨R,_,h⟩
    exact ⟨Submodule.span ℤ (R : Set M),h⟩

theorem realize_kernel {rows : Finset W} {close : W → M} {clash : W → Finset M}
    {P : Submodule ℤ M} (H : bad rows close clash P) :
    ∀ w∈rows, P.mkQ (close w)=0 → ∃ x∈clash w, P.mkQ x=0 := by
  intro w hw h
  have h' : close w∈P := by
    rw [←Submodule.ker_mkQ P]
    exact LinearMap.mem_ker.mpr h
  obtain ⟨x,hx,e⟩ := H w hw h'
  have e' : x∈LinearMap.ker P.mkQ := by rwa [Submodule.ker_mkQ]
  exact ⟨x,hx,LinearMap.mem_ker.mp e'⟩

omit [DecidableEq M] [DecidableEq W] in
theorem restrict_vocabulary {rows : Finset W} {close : W → M} {clash : W → Finset M}
    {P Q : Submodule ℤ M}
    (hclose : ∀ w∈rows, close w∈Q → close w∈P)
    (hclash : ∀ w∈rows, ∀ x∈clash w, x∈P → x∈Q)
    (H : bad rows close clash P) : bad rows close clash Q := by
  intro w hw hc
  obtain ⟨x,hx,hP⟩ := H w hw (hclose w hw hc)
  exact ⟨x,hx,hclash w hw x hx hP⟩

end AbelianCycleChart
#print axioms AbelianCycleChart.finite_span_criterion
#print axioms AbelianCycleChart.realize_kernel
#print axioms AbelianCycleChart.restrict_vocabulary
