import ActivePairPrune
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (ω ν : Measure X) [IsFiniteMeasure ω] [IsFiniteMeasure ν]

noncomputable def oneOn (A : Set X) : X→ℝ := A.indicator (fun _ => 1)

lemma flipped_indicator_rows (K : Kernel X) (B A : Set X) (ma : MeasurableSet A)
    (h : ∀ᵐ v ∂ν,(fun x => K.W (v,x)) =ᵐ[ω.restrict B] (fun _=>oneOn A v)) :
    ∀ᵐ x ∂ω.restrict B,(fun v => K.W (x,v)) =ᵐ[ν] oneOn A := by
  have mm : MeasurableSet {z:X×X | K.W z=oneOn A z.1} :=
    measurableSet_eq_fun K.measurable_W ((measurable_const.indicator ma).comp measurable_fst)
  have e := (Measure.ae_ae_comm mm).mp h
  filter_upwards [e] with x hx
  filter_upwards [hx] with v hv
  exact (K.symm x v).trans hv

/-- A saturated positive-mass pair determines complementary half-mass anchor
parts, at the level of both directions of the row restriction. -/
theorem active_pair_anchor_halves (K : Kernel X) (P Q : Set X)
    (hp : 0<ω.real P) (hq : 0<ω.real Q)
    (sat : ∀ᵐ x ∂ω, mass ν/2≤deg ν K x)
    (h : ∀ᵐ v ∂ν,
      ((∫ x in P,K.W (v,x) ∂ω)=ω.real P ∧ (∫ x in Q,K.W (v,x) ∂ω)=0) ∨
      ((∫ x in P,K.W (v,x) ∂ω)=0 ∧ (∫ x in Q,K.W (v,x) ∂ω)=ω.real Q)) :
    ∃ A : Set X, MeasurableSet A ∧
      ν.real A=mass ν/2 ∧ ν.real Aᶜ=mass ν/2 ∧
      (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict P] (fun _=>oneOn A v)) ∧
      (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict Q] (fun _=>oneOn Aᶜ v)) ∧
      (∀ᵐ x ∂ω.restrict P,(fun v=>K.W (x,v)) =ᵐ[ν] oneOn A) ∧
      (∀ᵐ x ∂ω.restrict Q,(fun v=>K.W (x,v)) =ᵐ[ν] oneOn Aᶜ) := by
  obtain ⟨A,ma,ap,aq⟩ := paired_indicator_partition ω ν K P Q hp h
  have fP := flipped_indicator_rows ω ν K P A ma ap
  have fQ := flipped_indicator_rows ω ν K Q Aᶜ ma.compl aq
  have lower (B C : Set X) (mC : MeasurableSet C) (b : 0<ω.real B)
      (e : ∀ᵐ x ∂ω.restrict B,(fun v=>K.W (x,v)) =ᵐ[ν] oneOn C) : mass ν/2≤ν.real C := by
    have e' := sat.filter_mono (Measure.restrict_le_self (s:=B)).absolutelyContinuous.ae_le
    have H : ∀ᵐ _ : X ∂ω.restrict B, mass ν/2≤ν.real C := by
      filter_upwards [e,e'] with x hx hs
      have inte : deg ν K x=ν.real C := by
        unfold deg
        rw [integral_congr_ae hx,oneOn,integral_indicator mC,setIntegral_const,smul_eq_mul,mul_one]
      rwa [←inte]
    by_contra n
    have hz : (ω.restrict B) univ=0 := by
      simpa only [ae_iff, n, not_false_eq_true, setOf_true] using H
    rw [Measure.restrict_apply_univ] at hz
    simp [measureReal_def,hz] at b
  have lp := lower P A ma hp fP
  have lq := lower Q Aᶜ ma.compl hq fQ
  have sum : ν.real A+ν.real Aᶜ=mass ν := by
    rw [←measureReal_union disjoint_compl_right ma.compl,union_compl_self,mass]
  exact ⟨A,ma,by linarith,by linarith,ap,aq,fP,fQ⟩

#print axioms active_pair_anchor_halves
end SparseHalfGraphon
