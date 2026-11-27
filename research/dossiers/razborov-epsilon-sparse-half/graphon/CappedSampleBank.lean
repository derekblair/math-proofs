import BankClassify
import ObstructionSequence

open Set MeasureTheory Function Filter Topology
open scoped ENNReal BigOperators
namespace SparseHalfGraphon

/-- Any saturated cut limit of the actual finite obstructing samples has
the active bank, with each side cap coming from a common finite anchor. -/
theorem capped_sample_bank {V : ℕ → Type*}
    [∀ k, Fintype (V k)] [∀ k, MeasurableSpace (V k)] [∀ k, MeasurableSingletonClass (V k)]
    (G : ∀ k, V k → V k → Bool) (sym : ∀ k u v, G k u v=G k v u)
    (tf : ∀ k u v w, G k u v=true → G k u w=true → G k v w=false)
    (α : ℕ→ℝ) (ht : Tendsto α atTop (𝓝 (2/5)))
    (cap : ∀ k (s : Finset (V k)), IndependentCells (G k) (s:Set (V k)) →
      (s.card:ℝ)/(Fintype.card (V k):ℝ)≤α k)
    (L : Kernel UnitHalfOpen) (c : ∀ k, V k→Fin 2) (d : UnitHalfOpen→Fin 2)
    (hc : ∀ k, Measurable (c k)) (hd : Measurable d) (i : Fin 2)
    (hI : ∀ k, IndependentCells (G k) (cell (c k) i))
    (hA : unitμ.real (cell d i)=2/5)
    (hTri : t3 unitμ L L L=0)
    (hSat : ∀ᵐ y ∂unitμ, y∉cell d i → 1/5≤deg (unitμ.restrict (cell d i)) L y)
    (ha : ∀ ε>0, ∀ᶠ k in atTop, ∃ π : Measure (V k×UnitHalfOpen),
      MeasurePreserving Prod.fst π uniformVertices ∧ MeasurePreserving Prod.snd π unitμ ∧
      π univ=1 ∧ π.real (labelMismatch (c k) d)≤ε ∧
      CutBound π (pullKernel (adjacencyKernel (G k) (sym k)) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε) :
    ∃ (I : Type) (_ : Countable I) (_ : Nonempty I), Nonempty (ActiveBank unitμ L (cell d i) I) := by
  let A := cell d i
  let ν := unitμ.restrict A
  let ω := unitμ.restrict Aᶜ
  have mA : MeasurableSet A := hd (measurableSet_singleton i)
  have hM : mass ν=2/5 := by simp [ν,mass,A,hA]
  have hn : ν univ≠0 := by
    intro h
    change (ν univ).toReal=2/5 at hM
    norm_num [h] at hM
  have hω : ω ≪ unitμ := Measure.restrict_le_self.absolutelyContinuous
  have hν : ν ≪ unitμ := Measure.restrict_le_self.absolutelyContinuous
  have hs : ∀ᵐ y ∂ω, mass ν/2≤deg ν L y := by
    have h := hSat.filter_mono hω.ae_le
    filter_upwards [h,ae_restrict_mem (μ:=unitμ) mA.compl] with y hy ho
    rw [hM,show (2/5:ℝ)/2=1/5 by norm_num]
    exact hy ho
  obtain ⟨I,ic,inn,P,Q,R,meas,innP,innQ,out,edge,act,prof⟩ :=
    saturated_active_pairs unitμ ω ν hω hν L hn Aᶜ mA.compl (ae_restrict_mem mA.compl)
      ((zero_triangle_iff_ae unitμ L).mp hTri) hs
  have cP : ∀ j, unitμ.real (P j)≤1/5 ∧ unitμ.real (Q j)≤1/5 := by
    exact active_family_side_caps unitμ G sym tf α ht cap L c d hc hd i hI ha hA
      P Q R meas innP innQ out edge act prof
  exact ⟨I,ic,inn,⟨⟨P,Q,R,meas,innP,innQ,out,edge,act,prof,cP⟩⟩⟩

#print axioms capped_sample_bank
end SparseHalfGraphon
