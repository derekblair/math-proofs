import CycleFiveStep

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def isolateCells (A S P Q : Set X) : Fin 5→Set X :=
  ![A∩S,P,Q,A∩Sᶜ,(A∪P∪Q)ᶜ]

lemma isolate_cells (A S P Q : Set X) (hA : MeasurableSet A) (hS : MeasurableSet S)
    (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (ap : Disjoint A P) (aq : Disjoint A Q) (pq : Disjoint P Q) :
    Cells (isolateCells A S P Q) := by
  constructor
  · intro i
    fin_cases i
    · exact hA.inter hS
    · exact hP
    · exact hQ
    · exact hA.inter hS.compl
    · exact ((hA.union hP).union hQ).compl
  · have ar : Disjoint A (A∪P∪Q)ᶜ := disjoint_compl_right.mono_left
      (subset_union_left.trans subset_union_left)
    have pr : Disjoint P (A∪P∪Q)ᶜ := disjoint_compl_right.mono_left
      (subset_union_right.trans subset_union_left)
    have qr : Disjoint Q (A∪P∪Q)ᶜ := disjoint_compl_right.mono_left subset_union_right
    intro i j h
    fin_cases i <;> fin_cases j <;> try (exfalso; exact h rfl)
    all_goals first
      | exact ap.mono_left inter_subset_left
      | exact aq.mono_left inter_subset_left
      | exact ar.mono_left inter_subset_left
      | exact ap.symm.mono_right inter_subset_left
      | exact aq.symm.mono_right inter_subset_left
      | exact ar.symm.mono_right inter_subset_left
      | exact pq | exact pq.symm
      | exact pr | exact pr.symm
      | exact qr | exact qr.symm
      | exact disjoint_compl_right.mono inter_subset_right inter_subset_right
      | exact disjoint_compl_left.mono inter_subset_right inter_subset_right

lemma isolate_cover (A S P Q : Set X) (x : X) : ∃ i,x∈isolateCells A S P Q i := by
  by_cases ha : x∈A
  · by_cases hs : x∈S
    · exact ⟨0,⟨ha,hs⟩⟩
    · exact ⟨3,⟨ha,hs⟩⟩
  · by_cases hp : x∈P
    · exact ⟨1,hp⟩
    · by_cases hq : x∈Q
      · exact ⟨2,hq⟩
      · refine ⟨4,?_⟩
        change x∉A∪P∪Q
        simp [ha,hp,hq]

lemma isolate_mass (A S P Q : Set X) (hA : MeasurableSet A) (hS : MeasurableSet S)
    (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (ap : Disjoint A P) (aq : Disjoint A Q) (pq : Disjoint P Q)
    (N : μ.real univ=1) (ma : μ.real A=2/5) (ms : μ.real (A∩S)=1/5)
    (mp : μ.real P=1/5) (mq : μ.real Q=1/5) :
    ∀ i,μ.real (isolateCells A S P Q i)=1/5 := by
  have mt := split_real μ A S hA hS
  have mr := measureReal_add_measureReal_compl (μ:=μ) ((hA.union hP).union hQ)
  rw [measureReal_union (disjoint_union_left.mpr ⟨aq,pq⟩) hQ,
    measureReal_union ap hP] at mr
  intro i
  fin_cases i
  · exact ms
  · exact mp
  · exact mq
  · change μ.real (A∩Sᶜ)=_
    linarith
  · change μ.real (A∪P∪Q)ᶜ=_
    linarith

private theorem rect_mono {R S T U : Set X} (h : R⊆T) (g : S⊆U) :
    (μ.restrict R).prod (μ.restrict S) ≤ (μ.restrict T).prod (μ.restrict U) := by
  rw [Measure.prod_restrict,Measure.prod_restrict]
  exact Measure.restrict_mono_set _ (Set.prod_mono h g)

private theorem rect_symm (K : Kernel X) (R S : Set X)
    (h : ∀ᵐ z ∂(μ.restrict R).prod (μ.restrict S),K.W z=0) :
    ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict R),K.W z=0 := by
  have t := (Measure.measurePreserving_swap (μ:=μ.restrict S) (ν:=μ.restrict R)).quasiMeasurePreserving.ae h
  filter_upwards [t] with ⟨x,y⟩ hz
  change K.W (y,x)=0 at hz
  rwa [K.symm y x] at hz

/-- Actual a.e. rigidity in the large-isolate chamber. There are no
assumptions about cross adjacency from the isolate pool into A; if
either such allowed rectangle is incomplete, a strict half exists. -/
theorem large_isolate_cycle (K : Kernel X) (A S P Q : Set X)
    (hA : MeasurableSet A) (hS : MeasurableSet S) (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (ap : Disjoint A P) (aq : Disjoint A Q) (pq : Disjoint P Q)
    (N : μ.real univ=1) (ma : μ.real A=2/5) (ms : μ.real (A∩S)=1/5)
    (mp : μ.real P=1/5) (mq : μ.real Q=1/5)
    (anchor : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A),K.W z=0)
    (cp : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict P),
      K.W z=S.indicator (fun _ => (1:ℝ)) z.1)
    (cq : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict Q),
      K.W z=(Sᶜ).indicator (fun _ => (1:ℝ)) z.1)
    (out : ∀ᵐ z ∂(μ.restrict Aᶜ).prod (μ.restrict Aᶜ), K.W z=0 ∨
      (z.1∈P ∧ z.2∈Q) ∨ (z.1∈Q ∧ z.2∈P)) :
    let D := isolateCells A S P Q
    let B := isolate_cells A S P Q hA hS hP hQ ap aq pq
    (∃ H : Half μ,halfEnergy μ K H<1/50) ∨
      K.W =ᵐ[μ.prod μ] (stepKernel D c5 B c5_sym).W := by
  intro D B
  let R := (A∪P∪Q)ᶜ
  have pO : P⊆Aᶜ := fun x hx ha => Set.disjoint_left.mp ap ha hx
  have qO : Q⊆Aᶜ := fun x hx ha => Set.disjoint_left.mp aq ha hx
  have rO : R⊆Aᶜ := fun x hx ha => hx (Or.inl (Or.inl ha))
  have rm : MeasurableSet R := ((hA.union hP).union hQ).compl
  have qr : Disjoint Q R := disjoint_compl_right.mono_left subset_union_right
  have pr : Disjoint P R := disjoint_compl_right.mono_left (subset_union_right.trans subset_union_left)
  let Zero := fun U V : Set X => ∀ᵐ z ∂(μ.restrict U).prod (μ.restrict V), K.W z=0
  have anc (U V : Set X) (u : U⊆A) (v : V⊆A) : Zero U V :=
    ae_mono (rect_mono μ u v) anchor
  have op (U V : Set X) (u : U⊆Aᶜ) (v : V⊆Aᶜ)
      (hu : MeasurableSet U) (hv : MeasurableSet V)
      (impossible : ∀ x∈U, ∀ y∈V, ¬ ((x∈P ∧ y∈Q) ∨ (x∈Q ∧ y∈P))) : Zero U V := by
    have m : ∀ᵐ z ∂(μ.restrict U).prod (μ.restrict V),z∈U ×ˢ V := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (hu.prod hv)
    filter_upwards [m,ae_mono (rect_mono μ u v) out] with z hz he
    exact he.resolve_right (impossible z.1 hz.1 z.2 hz.2)
  have qp0 : Zero P P := op P P pO pO hP hP (fun _ hx _ hy h => by
    rcases h with h|h
    · exact Set.disjoint_left.mp pq hy h.2
    · exact Set.disjoint_left.mp pq hx h.1)
  have qq0 : Zero Q Q := op Q Q qO qO hQ hQ (fun _ hx _ hy h => by
    rcases h with h|h
    · exact Set.disjoint_left.mp pq h.1 hx
    · exact Set.disjoint_left.mp pq h.2 hy)
  have rP0 : Zero P R := op P R pO rO hP rm (fun _ hx _ hy h => by
    rcases h with h|h
    · exact Set.disjoint_left.mp qr h.2 hy
    · exact Set.disjoint_left.mp pr h.2 hy)
  have rQ0 : Zero Q R := op Q R qO rO hQ rm (fun _ hx _ hy h => by
    rcases h with h|h
    · exact Set.disjoint_left.mp qr h.2 hy
    · exact Set.disjoint_left.mp pr h.2 hy)
  have rr0 : Zero R R := op R R rO rO rm rm (fun _ hx _ hy h => by
    rcases h with h|h
    · exact Set.disjoint_left.mp qr h.2 hy
    · exact Set.disjoint_left.mp pr h.2 hy)
  have cross_0 : Zero (A∩S) Q := by
    have m : ∀ᵐ z ∂(μ.restrict (A∩S)).prod (μ.restrict Q), z∈(A∩S) ×ˢ Q := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem ((hA.inter hS).prod hQ)
    filter_upwards [m,ae_mono (rect_mono μ inter_subset_left (Subset.refl Q)) cq] with z hz e
    exact e.trans (indicator_of_notMem (fun (hh : z.1∈Sᶜ) => hh hz.1.2) _)
  have cross_3 : Zero (A∩Sᶜ) P := by
    have m : ∀ᵐ z ∂(μ.restrict (A∩Sᶜ)).prod (μ.restrict P), z∈(A∩Sᶜ) ×ˢ P := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem ((hA.inter hS.compl).prod hP)
    filter_upwards [m,ae_mono (rect_mono μ inter_subset_left (Subset.refl P)) cp] with z hz e
    exact e.trans (indicator_of_notMem hz.1.2 _)
  have z (i j : Fin 5) (e : c5 i j=false) : Zero (D i) (D j) := by
    fin_cases i <;> fin_cases j <;> try (exfalso; revert e; decide)
    all_goals first
      | exact anc _ _ inter_subset_left inter_subset_left
      | exact cross_0 | exact cross_3
      | exact rect_symm μ K _ _ cross_0 | exact rect_symm μ K _ _ cross_3
      | exact qp0 | exact qq0 | exact rr0
      | exact rP0 | exact rQ0
      | exact rect_symm μ K _ _ rP0 | exact rect_symm μ K _ _ rQ0
  exact c5_step_rigidity μ K D B (ae_of_all _ (isolate_cover A S P Q))
    (isolate_mass μ A S P Q hA hS hP hQ ap aq pq N ma ms mp mq) z

#print axioms large_isolate_cycle
end SparseHalfCountableEndpoint
