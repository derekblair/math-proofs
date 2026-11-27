import ActiveCapAligned
open MeasureTheory Set Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

/-- Transfer the active-side independence cap from finite samples. No
upper bound on the independence number of the limit graphon is assumed. -/
theorem active_side_limit_cap {V : ℕ→Type*}
    [∀ k, Fintype (V k)] [∀ k, MeasurableSpace (V k)] [∀ k, MeasurableSingletonClass (V k)]
    {Y I : Type*} [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (G : ∀ k, V k→V k→Bool) (sym : ∀ k u v, G k u v=G k v u)
    (tf : ∀ k u v w, G k u v=true → G k u w=true → G k v w=false)
    (αs : ℕ→ℝ) (α : ℝ) (hα : Tendsto αs atTop (𝓝 α))
    (cap : ∀ k (s : Finset (V k)), IndependentCells (G k) (s : Set (V k)) →
      (s.card : ℝ)/(Fintype.card (V k) : ℝ) ≤ αs k)
    (L : Kernel Y) (c : ∀ k, V k→I) (d : Y→I) (hc : ∀ k, Measurable (c k))
    (hd : Measurable d) (i : I) (ind : ∀ k, IndependentCells (G k) (cell (c k) i))
    (S Q P T : Set Y) (sM : MeasurableSet S) (qM : MeasurableSet Q)
    (pM : MeasurableSet P) (tM : MeasurableSet T)
    (pOutside : P ⊆ (cell d i)ᶜ) (tInside : T ⊆ cell d i)
    (sPos : 0<ν.real S)
    (pS : ∀ᵐ y ∂ν, y∈P → deg (ν.restrict S) L y = ν.real S)
    (pQ : ∀ᵐ y ∂ν, y∈P → 0 < deg (ν.restrict Q) L y)
    (tQ : ∀ᵐ y ∂ν, y∈T → deg (ν.restrict Q) L y = ν.real Q)
    (ha : ∀ ε > 0, ∀ᶠ k in atTop, ∃ π : Measure (V k×Y),
      MeasurePreserving Prod.fst π uniformVertices ∧ MeasurePreserving Prod.snd π ν ∧
      π univ=1 ∧ π.real (labelMismatch (c k) d)≤ε ∧
      CutBound π (pullKernel (adjacencyKernel (G k) (sym k)) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε) :
    ν.real P + ν.real T ≤ α := by
  let sD := deg (ν.restrict S) L
  let qD := deg (ν.restrict Q) L
  let P' := P ∩ {y | sD y=ν.real S} ∩ {y | 0 < qD y}
  let T' := T ∩ {y | qD y=ν.real Q}
  have pEq : P' =ᵐ[ν] P := by
    filter_upwards [pS,pQ] with y hy hz
    apply propext
    change (y∈P ∧ sD y=ν.real S) ∧ 0<qD y ↔ y∈P
    exact ⟨fun H => H.1.1,fun H => ⟨⟨H,hy H⟩,hz H⟩⟩
  have tEq : T' =ᵐ[ν] T := by
    filter_upwards [tQ] with y hy
    apply propext
    change y∈T ∧ qD y=ν.real Q ↔ y∈T
    exact ⟨And.left,fun H => ⟨H,hy H⟩⟩
  have massP : ν.real P'=ν.real P := congrArg ENNReal.toReal (measure_congr pEq)
  have massT : ν.real T'=ν.real T := congrArg ENNReal.toReal (measure_congr tEq)
  have pM' : MeasurableSet P' := (pM.inter (measurableSet_eq_fun
    (deg_measurable _ L) measurable_const)).inter (measurableSet_lt measurable_const (deg_measurable _ L))
  have tM' : MeasurableSet T' := tM.inter (measurableSet_eq_fun (deg_measurable _ L) measurable_const)
  let trim (τ : ℝ) := P' ∩ {y | 2*τ<qD y}
  have trimCap (τ : ℝ) (tPos : 0 < τ) : ν.real (trim τ)+ν.real T' ≤ α := by
    have mtrim : MeasurableSet (trim τ) :=
      pM'.inter (measurableSet_lt measurable_const (deg_measurable _ L))
    by_contra! h
    let C := 3+2/(ν.real S/2)+4/τ
    have Cp : 0<C := by unfold C; positivity
    let e := (ν.real (trim τ)+ν.real T'-α)/(2*C)
    have ep : 0<e := div_pos (sub_pos.mpr h) (by positivity)
    obtain ⟨k,close,π,hp,hq,hπ,mismatch,cut⟩ :=
      ((hα.eventually_le_const (show α<α+e by linarith)).and (ha e ep)).exists
    letI : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
    have hC := active_cap_aligned ν π hp hq (G k) (sym k) (tf k) (αs k) (cap k)
      L (c k) d (hc k) hd i (ind k) S Q (trim τ) T' sM qM mtrim tM'
      (fun _ hx => pOutside hx.1.1.1) (fun _ hx => tInside hx.1)
      sPos τ tPos (fun _ hx => hx.1.1.2) (fun _ hx => hx.2) (fun _ hx => hx.2) e cut
    have hbound : ν.real (trim τ)+ν.real T' ≤ α+e*C := by
      calc
        _ ≤ α+e+2*e+(2*e)/(ν.real S/2)+2*((2*e)/τ) := by linarith
        _ = _ := by unfold C; ring
    have heq : e*C=(ν.real (trim τ)+ν.real T'-α)/2 := by
      unfold e
      field_simp
    linarith
  let seq (n : ℕ) : ℝ := 1/((n:ℝ)+1)/2
  have sp (n : ℕ) : 0<seq n := by unfold seq; positivity
  have sn : Antitone seq := by
    intro n m hm
    unfold seq
    exact div_le_div_of_nonneg_right
      (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)) (by norm_num)
  have mono : Monotone (fun n => trim (seq n)) := by
    intro n m hm x hx
    have hi := sn hm
    have hj : 2*seq n<qD x := hx.2
    exact ⟨hx.1,show 2*seq m < qD x by linarith⟩
  have H : P'=⋃ n,trim (seq n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0<qD x from hx.2)
      refine mem_iUnion.mpr ⟨n,hx,?_⟩
      change 2*(1/((n:ℝ)+1)/2)<qD x
      linarith
    · rintro hx
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact hn.1
  have hi : 0≤α-ν.real T' := by
    linarith [trimCap (seq 0) (sp 0),measureReal_nonneg (μ:=ν) (s:=trim (seq 0))]
  have bound : ν P' ≤ ENNReal.ofReal (α-ν.real T') := by
    rw [H,mono.measure_iUnion]
    apply iSup_le
    intro n
    have z : ν.real (trim (seq n))≤α-ν.real T' := by linarith [trimCap (seq n) (sp n)]
    have z' := ENNReal.ofReal_le_ofReal z
    unfold Measure.real at z'
    rwa [ENNReal.ofReal_toReal (measure_ne_top _ _)] at z'
  have r := (ENNReal.toReal_mono ENNReal.ofReal_ne_top bound).trans_eq (ENNReal.toReal_ofReal hi)
  change ν.real P' ≤ α-ν.real T' at r
  rw [massP,massT] at r
  linarith

#print axioms active_side_limit_cap
end SparseHalfGraphon
