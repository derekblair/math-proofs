import ActivePairLocal
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

theorem outside_pair_allocation (K : Kernel X) (S : Set X) (ms : MeasurableSet S) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i))
    (edge : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<K.W z → ∃ i,
      (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (a b : I→ℝ) (an : ∀ i,0≤a i) (bn : ∀ i,0≤b i)
    (al : ∀ i,a i≤μ.real (P i)) (bl : ∀ i,b i≤μ.real (Q i))
    (r : ℝ) (rn : 0≤r) (rl : r≤μ.real (S\⋃ i,P i∪Q i)) :
    ∃ D : X→ℝ, BMeas D ∧ (∀ x,0≤D x ∧ D x≤1) ∧ (∀ x∉S,D x=0) ∧
      (∫ x,D x ∂μ)= r+(∑' i,a i)+(∑' i,b i) ∧
      (∫ y, (∫ x,K.W (x,y)*D x ∂μ)*D y ∂μ)/2 ≤ ∑' i,a i*b i := by
  classical
  let C (i : I) := P i∪Q i
  let U : Set X := ⋃ i,C i
  let R := S\U
  have cm (i : I) : MeasurableSet (C i) := (mp i).union (mq i)
  have um : MeasurableSet U := MeasurableSet.iUnion cm
  have rm : MeasurableSet R := ms.diff um
  have us : U⊆S := iUnion_subset inside
  let T (i : Option I) := i.elim R C
  have tm (i : Option I) : MeasurableSet (T i) := by cases i; exact rm; exact cm _
  let g (i : Option I) := i.elim (allocSet μ R r)
    (fun j => allocSet μ (P j) (a j)+allocSet μ (Q j) (b j))
  have gm (i : Option I) : Measurable (g i) := by
    cases i with
    | none => exact (allocSet_bmeas μ R rm r rn rl).1
    | some j => exact ((allocSet_bmeas μ _ (mp j) _ (an j) (al j)).add
        (allocSet_bmeas μ _ (mq j) _ (bn j) (bl j))).1
  have rd (i : I) : Disjoint R (C i) := by
    apply Set.disjoint_left.mpr
    exact fun x hx h => hx.2 (mem_iUnion.mpr ⟨i,h⟩)
  have td : Pairwise (Disjoint on T) := by
    intro i j ne
    cases i <;> cases j
    · contradiction
    · exact rd _
    · exact (rd _).symm
    · exact outer (fun h => ne (congrArg some h))
  obtain ⟨f,fm,fe⟩ := exists_measurable_piecewise T tm g gm
    (fun _ _ ne _ h => False.elim (Set.disjoint_left.mp (td ne) h.1 h.2))
  let D := S.indicator f
  have off (x) (h : x∉S) : D x=0 := indicator_of_notMem h _
  have dOn (i : Option I) (x) (h : x∈T i) : D x=g i x := by
    have inc : T i⊆S := by cases i; exact sdiff_subset; exact inside _
    change S.indicator f x=_
    rw [indicator_of_mem (inc h)]
    exact fe i h
  have onP (i x) (hx : x∈P i) : D x=allocSet μ (P i) (a i) x := by
    rw [dOn (some i) x (Or.inl hx)]
    have hn : x∉Q i := fun hb=>Set.disjoint_left.mp (inner i) hx hb
    simp [g,allocSet,hn]
  have onQ (i x) (hx : x∈Q i) : D x=allocSet μ (Q i) (b i) x := by
    rw [dOn (some i) x (Or.inr hx)]
    have hn : x∉P i := fun ha=>Set.disjoint_left.mp (inner i) ha hx
    simp [g,allocSet,hn]
  have unit (x) : 0≤D x ∧ D x≤1 := by
    by_cases hs : x∈S
    · by_cases hu : x∈U
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hu
        rcases hi with hp|hq
        · rw [onP i x hp]
          exact ⟨allocSet_nn μ _ _ (an i) _,allocSet_le μ _ _ (al i) _⟩
        · rw [onQ i x hq]
          exact ⟨allocSet_nn μ _ _ (bn i) _,allocSet_le μ _ _ (bl i) _⟩
      · rw [dOn none x ⟨hs,hu⟩]
        exact ⟨allocSet_nn μ _ _ rn _,allocSet_le μ _ _ rl _⟩
    · simp [off x hs]
  have db := BMeas.of_unit (fm.indicator ms) (fun x=>(unit x).1) (fun x=>(unit x).2)
  have di := bMeas_integrable μ db
  have massSet (B : Set X) (mB : MeasurableSet B) (c : ℝ) (cn : 0≤c) (cl : c≤μ.real B)
      (agree : ∀ x∈B,D x=allocSet μ B c x) : (∫ x in B,D x ∂μ)=c := by
    rw [setIntegral_congr_fun mB agree, ←integral_indicator mB]
    have eq : B.indicator (allocSet μ B c)=allocSet μ B c := by
      ext x
      by_cases hx : x∈B <;> simp [allocSet,hx]
    rw [eq,allocSet_mass μ _ mB _ cn cl]
  have massP (i) := massSet _ (mp i) _ (an i) (al i) (onP i)
  have massQ (i) := massSet _ (mq i) _ (bn i) (bl i) (onQ i)
  have massR := massSet _ rm _ rn rl (dOn none)
  have dsP : Pairwise (Disjoint on P) := fun i j n=>(outer n).mono subset_union_left subset_union_left
  have dsQ : Pairwise (Disjoint on Q) := fun i j n=>(outer n).mono subset_union_right subset_union_right
  have sa := Summable.of_nonneg_of_le an al (real_mass_hasSum μ P mp dsP).summable
  have sb := Summable.of_nonneg_of_le bn bl (real_mass_hasSum μ Q mq dsQ).summable
  have split (f : X→ℝ) (fi : Integrable f μ) (fo : ∀ x∉S,f x=0) :
      (∫ x,f x ∂μ)=(∫ x in R,f x ∂μ)+∑' i, ((∫ x in P i,f x ∂μ)+(∫ x in Q i,f x ∂μ)) := by
    have e : S.indicator f=f := by
      ext x; by_cases h : x∈S <;> simp [h,fo]
    have cover : R∪U=S := by
      ext x; constructor
      · rintro (h|h); exact h.1; exact us h
      · intro h; by_cases u : x∈U; exact Or.inr u; exact Or.inl ⟨h,u⟩
    have dis : Disjoint R U := Set.disjoint_left.mpr (fun _ h hu=>h.2 hu)
    calc
      (∫ x,f x ∂μ)=(∫ x in S,f x ∂μ) := by rw [←integral_indicator ms,e]
      _ = (∫ x in R,f x ∂μ)+(∫ x in U,f x ∂μ) := by
        rw [←cover,setIntegral_union dis um fi.integrableOn fi.integrableOn]
      _ = _ := by
        rw [integral_iUnion cm outer fi.integrableOn]
        have each (i : I) : (∫ x in C i,f x ∂μ)=
            (∫ x in P i,f x ∂μ)+(∫ x in Q i,f x ∂μ) :=
          setIntegral_union (inner i) (mq i) fi.integrableOn fi.integrableOn
        simp_rw [each]
  refine ⟨D,db,unit,off,?_,?_⟩
  · rw [split D di off,massR]
    simp_rw [massP,massQ]
    rw [sa.tsum_add sb]
    ring
  have base := Measure.ae_ae_of_ae_prod edge
  let l (y : X) := ∫ x,K.W (x,y)*D x ∂μ
  let E (y : X) := l y*D y
  have Im (y : X) : Integrable (fun x=>K.W (x,y)*D x) μ := by
    have bw := BMeas.of_unit (K.measurable_W.comp (measurable_id.prodMk measurable_const))
      (fun x=>K.nonneg (x,y)) (fun x=>K.le_one (x,y))
    exact bMeas_integrable μ (bw.mul db)
  have lm : Measurable l :=
    (K.measurable_W.mul (db.1.comp measurable_fst)).stronglyMeasurable.integral_prod_left'.measurable
  have ln (y) : 0≤l y := integral_nonneg (fun x=>mul_nonneg (K.nonneg _) (unit x).1)
  have ll (y) : l y≤mass μ := by
    have h := integral_mono (Im y) (integrable_const (1:ℝ))
      (fun x=>(mul_le_mul_of_nonneg_right (K.le_one _) (unit x).1).trans (by simpa using (unit x).2))
    simpa [l,mass,smul_eq_mul] using h
  have ei : Integrable E μ := integrable_bounded μ (lm.mul db.1)
    (fun y=>mul_nonneg (ln y) (unit y).1)
    (fun y=>(mul_le_mul_of_nonneg_left (unit y).2 (ln y)).trans_eq (mul_one _)|>.trans (ll y))
  have load_bound (y : X) (B : Set X) (hB : MeasurableSet B)
      (hb : ∀ᵐ x ∂μ, x∈S → 0<K.W (x,y) → x∈B) : l y≤∫ x in B,D x ∂μ := by
    rw [←integral_indicator hB]
    apply integral_mono_ae (Im y) (di.indicator hB)
    filter_upwards [hb] with x h
    by_cases hx : x∈B
    · rw [indicator_of_mem hx]
      simpa using mul_le_mul_of_nonneg_right (K.le_one (x,y)) (unit x).1
    · rw [indicator_of_notMem hx]
      by_cases hs : x∈S
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt (fun hp=>hx (h hs hp))) (unit x).1
      · simp [off x hs]
  have Rzero : (∫ y in R,E y ∂μ)=0 := by
    have Z : E =ᵐ[μ.restrict R] (fun _=>0) := by
      filter_upwards [base.filter_mono (Measure.restrict_le_self (s:=R)).absolutelyContinuous.ae_le,
        ae_restrict_mem (μ:=μ) rm] with y hy ry
      have ld : l y≤0 := by
        simpa using load_bound y ∅ MeasurableSet.empty (by
          filter_upwards [hy] with x h hx hpos
          have pos : 0<K.W (y,x) := by simpa only [K.symm y x] using hpos
          obtain ⟨i,hc⟩ := h ry.1 hx pos
          exact False.elim (ry.2 (mem_iUnion.mpr ⟨i,hc.elim (fun j=>Or.inl j.1) (fun j=>Or.inr j.1)⟩)))
      change l y * D y = 0
      rw [le_antisymm ld (ln y),zero_mul]
    rw [integral_congr_ae Z,integral_zero]
  have conf (i : I) (y x : X) (hp : y∈P i)
      (h : ∃ j,(y∈P j∧x∈Q j)∨(y∈Q j∧x∈P j)) : x∈Q i := by
    obtain ⟨j, hj⟩ := h
    have eu : i=j := by
      by_contra n
      exact Set.disjoint_left.mp (outer n) (Or.inl hp)
        (hj.elim (fun z=>Or.inl z.1) (fun z=>Or.inr z.1))
    subst j
    exact hj.elim (fun z=>z.2) (fun z=>False.elim (Set.disjoint_left.mp (inner i) hp z.1))
  have conf' (i : I) (y x : X) (hq : y∈Q i)
      (h : ∃ j,(y∈P j∧x∈Q j)∨(y∈Q j∧x∈P j)) : x∈P i := by
    obtain ⟨j, hj⟩ := h
    have eu : i=j := by
      by_contra n
      exact Set.disjoint_left.mp (outer n) (Or.inr hq)
        (hj.elim (fun z=>Or.inl z.1) (fun z=>Or.inr z.1))
    subst j
    exact hj.elim (fun z=>False.elim (Set.disjoint_left.mp (inner i) z.1 hq)) (fun z=>z.2)
  have costP (i : I) : (∫ y in P i,E y ∂μ)≤b i*a i := by
    have I : Integrable (fun y=>b i*D y) (μ.restrict (P i)) := di.integrableOn.const_mul _
    have h : (∫ y in P i,E y ∂μ)≤∫ y in P i,b i*D y ∂μ := by
      apply integral_mono_ae ei.integrableOn I
      filter_upwards [base.filter_mono (Measure.restrict_le_self (s:=P i)).absolutelyContinuous.ae_le,
        ae_restrict_mem (μ:=μ) (mp i)] with y hy yp
      have lb := load_bound y (Q i) (mq i) (by
        filter_upwards [hy] with x h hx pos
        exact conf i y x yp (h (inside i (Or.inl yp)) hx (by simpa only [K.symm y x] using pos)))
      rw [massQ] at lb
      exact mul_le_mul_of_nonneg_right lb (unit y).1
    rwa [integral_const_mul,massP] at h
  have costQ (i : I) : (∫ y in Q i,E y ∂μ)≤a i*b i := by
    have I : Integrable (fun y=>a i*D y) (μ.restrict (Q i)) := di.integrableOn.const_mul _
    have h : (∫ y in Q i,E y ∂μ)≤∫ y in Q i,a i*D y ∂μ := by
      apply integral_mono_ae ei.integrableOn I
      filter_upwards [base.filter_mono (Measure.restrict_le_self (s:=Q i)).absolutelyContinuous.ae_le,
        ae_restrict_mem (μ:=μ) (mq i)] with y hy yq
      have lb := load_bound y (P i) (mp i) (by
        filter_upwards [hy] with x h hx pos
        exact conf' i y x yq (h (inside i (Or.inr yq)) hx (by simpa only [K.symm y x] using pos)))
      rw [massP] at lb
      exact mul_le_mul_of_nonneg_right lb (unit y).1
    rwa [integral_const_mul,massQ] at h
  have se : Summable (fun i => (∫ y in P i,E y ∂μ)+(∫ y in Q i,E y ∂μ)) := by
    have h := (hasSum_integral_iUnion cm outer ei.integrableOn).summable
    convert h using 1
    ext i
    exact (setIntegral_union (inner i) (mq i) ei.integrableOn ei.integrableOn).symm
  have sx : Summable (fun i=>a i*b i) := Summable.of_nonneg_of_le (fun i=>mul_nonneg (an i) (bn i))
    (fun i=>(mul_le_mul_of_nonneg_left ((bl i).trans (measureReal_mono (subset_univ _))) (an i)))
    (sa.mul_right (mass μ))
  have H := se.tsum_le_tsum (fun i => by linarith [costP i,costQ i,mul_comm (a i) (b i)]) (sx.mul_left 2)
  rw [sx.tsum_mul_left] at H
  change (∫ y,E y ∂μ)/2≤_
  rw [split E ei (fun y hy=>by simp [E,off y hy]),Rzero,zero_add]
  linarith

#print axioms outside_pair_allocation
end SparseHalfGraphon
