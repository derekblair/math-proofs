import GeometricGraphEdit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Continuous

namespace RobustFolkman
open MeasureTheory Finset Set
open scoped BigOperators InnerProductSpace

variable {Ω S : Type*} [MeasurableSpace Ω] [Fintype S]

def fiberOf (f : Ω→S) (a : S) : Set Ω := {ω | f ω=a}

noncomputable def finiteGraphMass (μ : Measure Ω) (f : Ω→S) (a : S) : ℝ :=
  (μ (fiberOf f a)).toReal

omit [Fintype S] in
theorem finiteGraphMass_nonneg (μ : Measure Ω) (f : Ω→S) (a : S) :
    0≤finiteGraphMass μ f a := ENNReal.toReal_nonneg

theorem finiteGraphMass_total (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→S)
    (meas : ∀ a, MeasurableSet (fiberOf f a)) :
    (∑ a, finiteGraphMass μ f a)=1 := by
  classical
  have dis : Pairwise fun a b => Disjoint (fiberOf f a) (fiberOf f b) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have cover : (⋃ a, fiberOf f a)=Set.univ := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
    exact ⟨f ω,rfl⟩
  have h : (∑ a, μ (fiberOf f a))=1 := by
    have q := measure_iUnion (μ:=μ) dis meas
    rw [cover,measure_univ] at q
    simpa only [tsum_fintype] using q.symm
  unfold finiteGraphMass
  rw [←ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _),h,ENNReal.toReal_one]

theorem finiteGraphMass_event (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→S)
    (meas : ∀ a, MeasurableSet (fiberOf f a)) (P : S→Prop) [DecidablePred P] :
    (∑ a, if P a then finiteGraphMass μ f a else 0) =
      (μ {ω | P (f ω)}).toReal := by
  classical
  let part (a : S) := if P a then fiberOf f a else ∅
  have pm (a : S) : MeasurableSet (part a) := by
    dsimp [part]
    split
    · exact meas _
    · exact MeasurableSet.empty
  have dis : Pairwise fun a b => Disjoint (part a) (part b) := by
    intro a b ne
    by_cases ha : P a <;> by_cases hb : P b
    · simp only [part,ha,hb,ite_true]
      exact Set.disjoint_left.mpr fun _ x y => ne (x.symm.trans y)
    · simp [part,hb]
    · simp [part,ha]
    · simp [part,ha]
  have cover : (⋃ a, part a) = {ω | P (f ω)} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a,pa⟩
      by_cases h : P a
      · have eq : f ω=a := by simpa [part,h,fiberOf] using pa
        exact eq.symm ▸ h
      · simp [part,h] at pa
    · intro h
      exact ⟨f ω,by simp [part,h,fiberOf]⟩
  have eq := measure_iUnion (μ:=μ) dis pm
  rw [cover,tsum_fintype] at eq
  rw [eq,ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [part,h,finiteGraphMass]

variable {V E : Type*} [Fintype V] [DecidableEq V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0:E) 1

noncomputable def pointGraph (t : ℝ) (x : V→UnitSphere E) : EdgeGraph V := by
  classical
  exact ((Finset.univ : Finset (V×V)).filter fun uv : V×V => uv.1≠uv.2 ∧ t≤⟪(x uv.1 : E),(x uv.2 : E)⟫_ℝ).image
    (fun uv => {uv.1,uv.2})

theorem measurable_pointGraph_edge (t : ℝ) (e : Finset V) :
    MeasurableSet {x : V→UnitSphere E | e∈pointGraph t x} := by
  classical
  have eq : {x : V→UnitSphere E | e∈pointGraph t x}
      = ⋃ uv : V×V, {x | uv.1≠uv.2 ∧ t≤⟪(x uv.1 : E),(x uv.2 : E)⟫_ℝ ∧ {uv.1,uv.2}=e} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    unfold pointGraph
    simp [Finset.mem_image,Finset.mem_filter,and_assoc]
  rw [eq]
  apply MeasurableSet.iUnion
  intro uv
  by_cases h : uv.1 ≠ uv.2 ∧ ({uv.1,uv.2}:Finset V)=e
  · have c₁ : Continuous (fun x : V→UnitSphere E => (x uv.1 : E)) :=
      continuous_subtype_val.comp (continuous_apply _)
    have c₂ : Continuous (fun x : V→UnitSphere E => (x uv.2 : E)) :=
      continuous_subtype_val.comp (continuous_apply _)
    have m := measurableSet_le (measurable_const (a:=t)) (c₁.inner c₂).measurable
    simpa [h.1,h.2] using m
  · have z : {x : V→UnitSphere E | uv.1≠uv.2 ∧ t≤⟪(x uv.1 : E),(x uv.2 : E)⟫_ℝ ∧
        ({uv.1,uv.2}:Finset V)=e}=∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false, iff_false]
      exact fun p => h ⟨p.1,p.2.2⟩
    rw [z]
    exact MeasurableSet.empty

theorem measurable_pointGraph_fiber (t : ℝ) (g : EdgeGraph V) :
    MeasurableSet (fiberOf (pointGraph (E:=E) t) g) := by
  classical
  have eq : fiberOf (pointGraph (E:=E) t) g =
    ⋂ e : Finset V, {x : V→UnitSphere E | e∈pointGraph t x ↔ e∈g} := by
    ext x
    rw [Set.mem_iInter]
    exact Finset.ext_iff
  rw [eq]
  apply MeasurableSet.iInter
  intro e
  by_cases h : e∈g
  · simpa [h] using measurable_pointGraph_edge (E:=E) t e
  · have z : {x : V→UnitSphere E | e∈pointGraph t x ↔ e∈g}
          ={x : V→UnitSphere E | e∈pointGraph t x}ᶜ := by
        ext x
        simp [h]
    rw [z]
    exact (measurable_pointGraph_edge (E:=E) t e).compl

theorem finite_spherical_graph_law (σ : Measure (UnitSphere E)) [IsProbabilityMeasure σ]
    (t : ℝ) :
    let μ : Measure (V→UnitSphere E) := Measure.pi fun _ => σ
    (∀ g : EdgeGraph V, 0≤finiteGraphMass μ (pointGraph t) g) ∧
    (∑ g : EdgeGraph V, finiteGraphMass μ (pointGraph t) g)=1 := by
  intro μ
  exact ⟨fun _ => finiteGraphMass_nonneg _ _ _,finiteGraphMass_total μ _ (measurable_pointGraph_fiber t)⟩

#print axioms finiteGraphMass_event
#print axioms finite_spherical_graph_law
end RobustFolkman
