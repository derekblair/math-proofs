import GeometricPairGraphs

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal BigOperators
variable {J S : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace S]

theorem sample_graph_removed_tail (σ : Measure S) [IsProbabilityMeasure σ]
    (A B : Set (S×S)) (am : MeasurableSet A) (bm : MeasurableSet B)
    (p q r : ℝ) (pp : 0<p) (qp : 0<q) (n : 0<Fintype.card J)
    (mass : (σ.prod σ).real (A\B)≤r*p^2*q) :
    let μ := Measure.pi (fun _ : J => σ)
    let M := (Fintype.card J:ℝ)^2*p^2*q
    μ.real {x : J→S | M/100<((samplePredicateGraph A x \ samplePredicateGraph B x).card:ℝ)}
      ≤100*r := by
  intro μ M
  have n0 : 0<(Fintype.card J:ℝ) := by exact_mod_cast n
  have mp : 0<M := by dsimp [M]; positivity
  let c := ENNReal.ofReal (M/100)
  have c0 : c≠0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have ct : c≠∞ := ENNReal.ofReal_ne_top
  have sub : {x : J→S | M/100<((samplePredicateGraph A x \ samplePredicateGraph B x).card:ℝ)}
      ⊆ {x | c≤samplePairCount (J:=J) (A\B) x} := by
    intro x hx
    have n : (M/100)≤((samplePredicateGraph A x \ samplePredicateGraph B x).card:ℝ) := le_of_lt hx
    have z := ENNReal.ofReal_le_ofReal n
    rw [ENNReal.ofReal_natCast] at z
    exact z.trans (samplePredicate_sdiff_count A B x)
  have card : ((offDiagonal : Finset (J×J)).card:ℝ)≤(Fintype.card J:ℝ)^2 := by
    have le := Finset.card_le_card (Finset.subset_univ (offDiagonal : Finset (J×J)))
    rw [Finset.card_univ,Fintype.card_prod] at le
    simpa only [Nat.cast_mul,pow_two] using (show ((offDiagonal : Finset (J×J)).card:ℝ)≤
      ((Fintype.card J*Fintype.card J:ℕ):ℝ) by exact_mod_cast le)
  have mark := samplePairCount_markov (J:=J) σ (A\B) (am.diff bm) c c0 ct
  have fin := ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top (offDiagonal : Finset (J×J)).card) (measure_ne_top (σ.prod σ) (A\B))) c0
  have h := ENNReal.toReal_mono fin ((measure_mono (μ:=μ) sub).trans mark)
  rw [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_natCast] at h
  have hc : c.toReal=M/100 := ENNReal.toReal_ofReal (by positivity)
  rw [hc] at h
  have e := mul_le_mul card mass ENNReal.toReal_nonneg (by positivity : 0≤(Fintype.card J:ℝ)^2)
  refine h.trans ?_
  apply (div_le_iff₀ (by positivity : 0<M/100)).2
  dsimp [M]
  convert e using 1 <;> first | rfl | ring

#print axioms sample_graph_removed_tail
end RobustFolkman.GeometricGap
