import AlignTables
import TableExtract

open Set MeasureTheory Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

theorem eventual_base_factor {I : ℕ → Type*} {X : ℕ → Type*} {Y : Type*}
    (P : ℕ → ∀ n, I (n+1) → I n) (p : ∀ n, I (n+1) → I n)
    (c : ∀ k n, X k → I n) (d : ∀ n, Y → I n)
    (hP : ∀ k n x, P k n (c k (n+1) x) = c k n x)
    (hp : ∀ n y, p n (d (n+1) y) = d n y)
    (hstab : ∀ n, ∀ᶠ k in atTop, P k n = p n) (n : ℕ) :
    ∃ f : I n → I 0, (∀ y, f (d n y) = d 0 y) ∧
      ∀ᶠ k in atTop, ∀ x, f (c k n x) = c k 0 x := by
  induction n with
  | zero => exact ⟨id, fun _ => rfl, Eventually.of_forall (fun _ _ => rfl)⟩
  | succ n ih =>
    obtain ⟨f,hf,hb⟩ := ih
    refine ⟨f ∘ p n, fun y => by rw [comp_apply,hp,hf],?_⟩
    filter_upwards [hb,hstab n] with k hk hkn x
    rw [comp_apply,← hkn,hP,hk]

/-- Compactness with marked base labels for a sequence with uniformly
bounded coherent tables and cut-good approximants. The coupling is
between each sample's own space and a fixed Lebesgue graphon. -/
theorem aligned_tower_compactness {X : ℕ → Type*} [∀ k, MeasurableSpace (X k)]
    (μ : ∀ k, Measure (X k)) [∀ k, IsFiniteMeasure (μ k)] (hμ : ∀ k, μ k univ = 1)
    (W : ∀ k, Kernel (X k)) (size : ℕ → ℕ)
    (P : ℕ → ∀ n, Fin (size (n+1)) → Fin (size n))
    (A : ∀ k, CoherentTables (fun n => Fin (size n)) (P k))
    (c : ∀ k n, X k → Fin (size n)) (hc : ∀ k n, Measurable (c k n))
    (href : ∀ k n x, P k n (c k (n+1) x) = c k n x)
    (hC : ∀ k n i, (μ k).real (cell (c k n) i) = (A k).cell n i)
    (J : ∀ k, ℕ → Kernel (X k))
    (hJ : ∀ k n x y, (J k n).W (x,y) = (A k).density n (c k n x) (c k n y))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hcut : ∀ k n, CutBound (μ k) (W k) (J k n) (δ n)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ L : Kernel UnitHalfOpen,
    ∃ d : UnitHalfOpen → Fin (size 0), Measurable d ∧
      ∀ ε > 0, ∀ᶠ k in atTop,
        ∃ π : Measure (X (q k) × UnitHalfOpen),
          MeasurePreserving Prod.fst π (μ (q k)) ∧ MeasurePreserving Prod.snd π unitμ ∧
          π univ = 1 ∧ π.real (labelMismatch (c (q k) 0) d) ≤ ε ∧
          CutBound π (pullKernel (W (q k)) Prod.fst measurable_fst)
            (pullKernel L Prod.snd measurable_snd) ε := by
  obtain ⟨q,p,B,hq,hp,hBt,hBJ⟩ := coherent_table_subsequence size P A
  obtain ⟨L,_,hL⟩ := B.unitStep_limit
  refine ⟨q,hq,L,B.unitLabel 0,B.unitLabel_meas 0,?_⟩
  intro ε he
  let e := ε / 5
  have he' : 0 < e := by dsimp [e]; positivity
  have hδ' := Metric.tendsto_nhds.mp hδ e he'
  obtain ⟨n,hLn, hδn⟩ := ((hL e he').and hδ').exists
  have hδle : δ n ≤ e := by
    rw [Real.dist_eq, sub_zero] at hδn
    exact ((le_abs_self _).trans hδn.le)
  obtain ⟨f,hfd,hfc⟩ := eventual_base_factor
    (fun k => P (q k)) p (fun k => c (q k)) B.unitLabel
    (fun k => href (q k)) B.unitLabel_parent hp n
  have hA := align_fixed_level B (fun k => μ (q k)) (fun k => hμ (q k))
    (fun k => A (q k)) n (fun k => c (q k) n) (fun k => hc (q k) n)
    (fun k => J (q k) n) (fun k => hC (q k) n) (fun k => hJ (q k) n)
    (hBt n) (hBJ n) e he'
  filter_upwards [hA,hfc] with k hk hfk
  obtain ⟨π,h₁,h₂,hπ,hmis,hstep⟩ := hk
  haveI : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
  refine ⟨π,h₁,h₂,hπ,?_,?_⟩
  · have hsub : labelMismatch (c (q k) 0) (B.unitLabel 0) ⊆
        labelMismatch (c (q k) n) (B.unitLabel n) := by
      intro z hz
      change c (q k) 0 z.1 ≠ B.unitLabel 0 z.2 at hz
      change c (q k) n z.1 ≠ B.unitLabel n z.2
      intro hh
      exact hz ((hfk z.1).symm.trans ((congrArg f hh).trans (hfd z.2)))
    have hle := (measureReal_mono (μ:=π) hsub).trans hmis
    exact hle.trans (by dsimp [e]; linarith)
  · have h₀ := cut_pull π (μ (q k)) Prod.fst h₁ _ _ (δ n) (hcut (q k) n)
    have h₃ := cut_pull π unitμ Prod.snd h₂ _ _ e hLn
    have h4 := cut_tri π _ _ _ _ _ (cut_tri π _ _ _ _ _ h₀ hstep) h₃
    intro s t hs ht
    have hle := h4 s t hs ht
    exact hle.trans (by dsimp [e] at hδle ⊢; linarith)

#print axioms aligned_tower_compactness
end SparseHalfGraphon
