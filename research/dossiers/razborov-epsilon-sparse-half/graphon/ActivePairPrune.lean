import PairedIndicatorRows
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (ω ν : Measure X) [IsFiniteMeasure ω]

lemma ae_edge_positive_degrees (K : Kernel X) :
    ∀ᵐ z ∂ω.prod ω, 0<K.W z → 0<deg ω K z.1 ∧ 0<deg ω K z.2 := by
  have hmeas : MeasurableSet {z : X×X | 0<K.W z → 0<deg ω K z.1} := by
    have eq : {z : X×X | 0<K.W z → 0<deg ω K z.1} =
        {z : X×X | 0<K.W z}ᶜ ∪ {z : X×X | 0<deg ω K z.1} := by
      ext z; simp [imp_iff_not_or]
    rw [eq]
    exact (measurableSet_lt measurable_const K.measurable_W).compl.union
      (measurableSet_lt measurable_const ((deg_measurable ω K).comp measurable_fst))
  have h₁ : ∀ᵐ z ∂ω.prod ω, 0<K.W z → 0<deg ω K z.1 := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    apply ae_of_all
    intro v
    by_cases hv : 0<deg ω K v
    · exact ae_of_all _ fun _ _ => hv
    · have d : deg ω K v=0 := le_antisymm (le_of_not_gt hv) (deg_nonneg ω K v)
      have z := (load_fiber_zero_or_one ω K v univ).1 (by simpa [deg] using d)
      simp only [Measure.restrict_univ] at z
      filter_upwards [z] with x H hx
      rw [H] at hx
      exact False.elim ((lt_irrefl 0) hx)
  have h₂ := (Measure.measurePreserving_swap (μ:=ω) (ν:=ω)).quasiMeasurePreserving.ae h₁
  filter_upwards [h₁,h₂] with z h1 h2 h
  refine ⟨h1 h,h2 ?_⟩
  change 0<K.W (z.2,z.1)
  rwa [K.symm]

lemma pairedRow_subset (K : Kernel X) (P Q p q : I→Set X)
    (hp : ∀ i, p i⊆P i) (hq : ∀ i, q i⊆Q i) (v : X)
    (h : PairedRow ω K P Q v) : PairedRow ω K p q v := by
  have row (A B : Set X) (z : B⊆A) :
      (((∫ x in A,K.W (v,x) ∂ω)=0) → (∫ x in B,K.W (v,x) ∂ω)=0) ∧
      (((∫ x in A,K.W (v,x) ∂ω)=ω.real A) → (∫ x in B,K.W (v,x) ∂ω)=ω.real B) := by
    have mono := (Measure.restrict_mono_set ω z).absolutelyContinuous.ae_le
    constructor
    · intro h
      rw [integral_congr_ae (((load_fiber_zero_or_one ω K v A).1 h).filter_mono mono),integral_zero]
    · intro h
      rw [integral_congr_ae (((load_fiber_zero_or_one ω K v A).2 h).filter_mono mono),
        setIntegral_const,smul_eq_mul,mul_one]
  intro i
  have pp := row _ _ (hp i)
  have qq := row _ _ (hq i)
  rcases h i with ⟨a,b⟩|⟨a,b⟩
  · exact Or.inl ⟨pp.2 a,qq.1 b⟩
  · exact Or.inr ⟨pp.1 a,qq.2 b⟩

/-- Drop all zero outside degree points, then discard entire pairs with a null
side. Countability ensures that this removes no positive outside edge a.e. -/
theorem prune_active_pairs
    (K : Kernel X) (S : Set X) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i∪Q i⊆S)
    (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i => P i∪Q i))
    (support : ∀ᵐ z ∂ω.prod ω, z.1∈S → z.2∈S → 0<K.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (cover : ∀ᵐ x ∂ω, x∈S)
    (root : ∀ᵐ v ∂ν, PairedRow ω K P Q v) :
    ∃ p q : I→Set X,
      (∀ i, MeasurableSet (p i)) ∧ (∀ i, MeasurableSet (q i)) ∧
      (∀ i, p i⊆P i ∧ q i⊆Q i) ∧
      (∀ i, (p i=∅ ∧ q i=∅) ∨ (0<ω.real (p i) ∧ 0<ω.real (q i))) ∧
      (∀ i, Disjoint (p i) (q i)) ∧ Pairwise (Disjoint on fun i => p i∪q i) ∧
      (∀ᵐ z ∂ω.prod ω, 0<K.W z → ∃ i,
        (z.1∈p i ∧ z.2∈q i) ∨ (z.1∈q i ∧ z.2∈p i)) ∧
      (∀ᵐ x ∂ω, x∈(⋃ i,p i∪q i) ↔ 0<deg ω K x) ∧
      (∀ᵐ v ∂ν, PairedRow ω K p q v) := by
  classical
  let L := {x | 0<deg ω K x}
  have lm : MeasurableSet L := measurableSet_lt measurable_const (deg_measurable ω K)
  let P₀ (i : I) := P i∩L
  let Q₀ (i : I) := Q i∩L
  let good (i : I) := 0<ω.real (P₀ i) ∧ 0<ω.real (Q₀ i)
  let p (i : I) := if good i then P₀ i else ∅
  let q (i : I) := if good i then Q₀ i else ∅
  have pm (i : I) : MeasurableSet (p i) := by by_cases h : good i <;> simp [p,h,P₀,mp,lm]
  have qm (i : I) : MeasurableSet (q i) := by by_cases h : good i <;> simp [q,h,Q₀,mq,lm]
  have ps (i : I) : p i⊆P₀ i := by by_cases h : good i <;> simp [p,h]
  have qs (i : I) : q i⊆Q₀ i := by by_cases h : good i <;> simp [q,h]
  have pp (i : I) : p i⊆P i := (ps i).trans inter_subset_left
  have qq (i : I) : q i⊆Q i := (qs i).trans inter_subset_left
  let Bad (T : I→Set X) := ⋃ i, if ω (T i)=0 then T i else ∅
  have bad0 (T : I→Set X) : ω (Bad T)=0 := by
    apply measure_iUnion_null
    intro i
    by_cases h : ω (T i)=0 <;> simp [h]
  have badAE (T : I→Set X) : ∀ᵐ z ∂ω, z∉Bad T := by
    apply ae_iff.mpr
    simpa using bad0 T
  have notBad (T : I→Set X) (x : X) (nx : x∉Bad T) (i : I) (hx : x∈T i) :
      0<ω.real (T i) := by
    have non : ω (T i)≠0 := by
      intro e
      exact nx (mem_iUnion.mpr ⟨i,by simp [e,hx]⟩)
    exact (ENNReal.toReal_pos_iff).mpr ⟨bot_lt_iff_ne_bot.mpr non,lt_top_iff_ne_top.mpr (measure_ne_top _ _)⟩
  have hsP := (Measure.quasiMeasurePreserving_fst (μ:=ω) (ν:=ω)).ae cover
  have hsQ := (Measure.quasiMeasurePreserving_snd (μ:=ω) (ν:=ω)).ae cover
  have no (T : I→Set X) : ∀ᵐ z ∂ω.prod ω, z.1∉Bad T ∧ z.2∉Bad T := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=ω) (ν:=ω)).ae (badAE T),
      (Measure.quasiMeasurePreserving_snd (μ:=ω) (ν:=ω)).ae (badAE T)] with z h1 h2
    exact ⟨h1,h2⟩
  have edge : ∀ᵐ z ∂ω.prod ω, 0<K.W z → ∃ i,
      (z.1∈p i ∧ z.2∈q i) ∨ (z.1∈q i ∧ z.2∈p i) := by
    filter_upwards [support,hsP,hsQ,ae_edge_positive_degrees ω K,no P₀,no Q₀] with z hz hS hT act bp bq h
    obtain ⟨d,e⟩ := act h
    obtain ⟨i,pair⟩ := hz hS hT h
    rcases pair with ⟨P1,Q2⟩|⟨Q1,P2⟩
    · have a : z.1∈P₀ i := ⟨P1,d⟩
      have b : z.2∈Q₀ i := ⟨Q2,e⟩
      have g : good i := ⟨notBad P₀ _ bp.1 i a,notBad Q₀ _ bq.2 i b⟩
      exact ⟨i,Or.inl ⟨by simpa [p,g] using a,by simpa [q,g] using b⟩⟩
    · have a : z.2∈P₀ i := ⟨P2,e⟩
      have b : z.1∈Q₀ i := ⟨Q1,d⟩
      have g : good i := ⟨notBad P₀ _ bp.2 i a,notBad Q₀ _ bq.1 i b⟩
      exact ⟨i,Or.inr ⟨by simpa [q,g] using b,by simpa [p,g] using a⟩⟩
  refine ⟨p,q,pm,qm,fun i=>⟨pp i,qq i⟩,?_,fun i=>(inner i).mono (pp i) (qq i),
    fun i j ne=>(outer ne).mono (union_subset_union (pp i) (qq i))
      (union_subset_union (pp j) (qq j)),edge,?_,?_⟩
  · intro i
    by_cases h : good i
    · exact Or.inr (by simpa only [p,q,if_pos h] using h)
    · exact Or.inl (by simp [p,q,h])
  · filter_upwards [Measure.ae_ae_of_ae_prod edge] with x hx
    constructor
    · intro h
      obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact hi.elim (fun hz => ((ps i) hz).2) (fun hz => ((qs i) hz).2)
    · intro h
      by_contra out
      have zeros : (fun y=>K.W (x,y))=ᵐ[ω](fun _=>(0:ℝ)) := by
        filter_upwards [hx] with y hy
        apply le_antisymm _ (K.nonneg _)
        by_contra! pos
        obtain ⟨i,j⟩ := hy pos
        exact out (mem_iUnion.mpr ⟨i,j.elim (fun z=>Or.inl z.1) (fun z=>Or.inr z.1)⟩)
      have deg0 : deg ω K x=0 := (integral_congr_ae zeros).trans (integral_zero X ℝ)
      linarith
  · filter_upwards [root] with v hv
    exact pairedRow_subset ω K P Q p q pp qq v hv

#print axioms prune_active_pairs
end SparseHalfGraphon
