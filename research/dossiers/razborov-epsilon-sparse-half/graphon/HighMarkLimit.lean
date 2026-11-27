import HighMarkTransport
open MeasureTheory Set Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

theorem highOutside_limit_cap {Z : ℕ → Type*} [∀ k, MeasurableSpace (Z k)]
    {Y I : Type*} [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : ∀ k, Measure (Z k)) [∀ k, IsFiniteMeasure (μ k)] (ν : Measure Y) [IsFiniteMeasure ν]
    (W : ∀ k, Kernel (Z k)) (L : Kernel Y)
    (c : ∀ k, Z k → I) (d : Y → I) (hc : ∀ k, Measurable (c k)) (hd : Measurable d) (i : I)
    (αs : ℕ → ℝ) (α : ℝ) (hα : Tendsto αs atTop (𝓝 α))
    (cap : ∀ᶠ k in atTop, (μ k).real
      (highOutside (μ k) (W k) (cell (c k) i) ((μ k).real (cell (c k) i)/2)) ≤ αs k)
    (ha : ∀ ε > 0, ∀ᶠ k in atTop, ∃ π : Measure (Z k×Y),
      MeasurePreserving Prod.fst π (μ k) ∧ MeasurePreserving Prod.snd π ν ∧
      π univ=1 ∧ π.real (labelMismatch (c k) d)≤ε ∧
      CutBound π (pullKernel (W k) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε) :
    ν.real (highOutside ν L (cell d i) (ν.real (cell d i)/2)) ≤ α := by
  let A := cell d i
  let base := ν.real A/2
  let H (δ : ℝ) := highOutside ν L A (base+δ)
  have margin (δ : ℝ) (hδ : 0 < δ) : ν.real (H δ) ≤ α := by
    by_contra! h
    let e := min δ ((ν.real (H δ)-α)/(2*(2+3/(δ/2))))
    have he : 0 < e := lt_min hδ (div_pos (sub_pos.mpr h) (by positivity))
    have hmin := min_le_right δ ((ν.real (H δ)-α)/(2*(2+3/(δ/2))))
    have eδ : e ≤ δ := min_le_left _ _
    obtain ⟨k,⟨hcap,hclose⟩,π,hp,hq,hπ,hmm,hcut⟩ :=
      ((cap.and (hα.eventually_le_const (show α < α+e by linarith))).and (ha e he)).exists
    letI : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
    have hp' : mass π=1 := by simp [mass,Measure.real,hπ]
    have E := highOutside_aligned (μ k) ν π hp' hp hq (c k) d (hc k) hd i (W k) L e δ
      hδ (hmm.trans eδ) hcut
    change ν.real (H δ) ≤ _ at E
    have D : (2*e+π.real (labelMismatch (c k) d))/(δ/2) ≤ (3*e)/(δ/2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    change e ≤ _ at hmin
    have H2 := (le_div_iff₀ (show 0<2*(2+3/(δ/2)) by positivity)).mp hmin
    have H3 : e*(2+3/(δ/2)) ≤ (ν.real (H δ)-α)/2 := by nlinarith only [H2]
    have G1 : ν.real (H δ) ≤ α + e*(2+3/(δ/2)) := by
      calc
        _ ≤ α+e+e+(3*e)/(δ/2) := by linarith only [E,hcap,hclose,hmm,D]
        _ = _ := by ring
    linarith
  let seq (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have sp (n : ℕ) : 0 < seq n := by unfold seq; positivity
  have sn : Antitone seq := by
    intro n m h
    unfold seq
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ h)
  have mono : Monotone (fun n => H (seq n)) := by
    intro n m hn x hx
    exact ⟨hx.1,(add_le_add (le_refl base) (sn hn)).trans_lt hx.2⟩
  have E : highOutside ν L A base = ⋃ n, H (seq n) := by
    ext y
    constructor
    · intro h
      have h' : base < deg (ν.restrict A) L y := h.2
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h')
      exact Set.mem_iUnion.mpr ⟨n,h.1,by simpa [seq,add_comm] using lt_sub_iff_add_lt.mp hn⟩
    · intro h
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
      exact ⟨hn.1,(lt_add_of_pos_right _ (sp n)).trans hn.2⟩
  change ν.real (highOutside ν L A base) ≤ α
  rw [E]
  have α0 : 0 ≤ α := measureReal_nonneg.trans (margin (seq 0) (sp 0))
  have bound : ν (⋃ n,H (seq n)) ≤ ENNReal.ofReal α := by
    rw [mono.measure_iUnion]
    apply iSup_le
    intro n
    have Q := ENNReal.ofReal_le_ofReal (margin (seq n) (sp n))
    unfold Measure.real at Q
    rwa [ENNReal.ofReal_toReal (measure_ne_top _ _)] at Q
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top bound).trans_eq (ENNReal.toReal_ofReal α0)

#print axioms highOutside_limit_cap
end SparseHalfGraphon
