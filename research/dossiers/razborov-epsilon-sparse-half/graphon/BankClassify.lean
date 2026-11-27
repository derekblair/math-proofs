import BankChambers

open Set MeasureTheory Function Filter
open scoped ENNReal BigOperators
namespace SparseHalfGraphon

def BalancedSparseTemplate {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (K : Kernel Y) : Prop :=
    (∃ g : Y → Fin 5, Measurable g ∧ (∀ i, μ.real (cell g i)=1/5) ∧
      K.W =ᵐ[μ.prod μ] (fun z => edgeReal (C5Stability.adj (g z.1) (g z.2)))) ∨
    (∃ g : Y → Fin 10, Measurable g ∧ (∀ i, μ.real (cell g i)=1/10) ∧
      K.W =ᵐ[μ.prod μ] (fun z => edgeReal (petersenBaseAdj (g z.1) (g z.2))))

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
variable {K : Kernel Y} {A : Set Y} {I : Type*}

/-- The saturated bank with extremal fractional half cost is an actual
balanced C5 or Petersen kernel, not just a dominated block completion. -/
theorem ActiveBank.classify [Countable I] [Nonempty I] (B : ActiveBank μ K A I) (hμ : μ.real univ=1) (hA : MeasurableSet A)
    (hAm : μ.real A=2/5)
    (hAI : energyPair μ K (indicatorWeight A) (indicatorWeight A)=0)
    (hb : 1/50≤beta μ K) : BalancedSparseTemplate μ K := by
  have hout : μ.real Aᶜ=3/5 := by linarith [mass_compl_add μ A hA,show mass μ=1 from hμ]
  have hZero := anchor_zero_of_energy hA hAI
  let mp := fun j => (B.meas j).1
  let mq := fun j => (B.meas j).2.1
  obtain ⟨θ,hθ0,hθ2,hcost⟩ :=
    outside_dual_ge_two_maxmin μ K Aᶜ hA.compl B.P B.Q mp mq B.inside B.inner B.outer B.edge B.cap hout hb
  obtain ⟨hSum,hT⟩ := paired_bank_measure μ Aᶜ B.P B.Q mp mq B.inside B.inner B.outer
  have hTotal : (∑' i, (B.p i+B.q i))+B.h=6 := by
    rw [hout] at hT
    dsimp [ActiveBank.p,ActiveBank.q,ActiveBank.h]
    linarith
  have hClass := SparseHalfCountableEndpoint.bank_dichotomy B.p B.q θ B.h
    ⟨hθ0,hθ2⟩ B.p_upper B.q_nonneg B.q_le_p hSum B.h_nonneg hTotal hcost
  rcases hClass with ⟨_,j,hp,hq,hrest⟩ | ⟨j,hq,hpivot⟩ | ⟨_,s,hs,hrest⟩ |
    ⟨i,j,ne,hi,hj,hh,hL,hrest⟩
  · exact Or.inl (B.c5_of_single_full hA hAm hμ hZero hb j hp hq (fun k hk=>(hrest k hk).1))
  · exfalso
    have hJ := B.cap j
    have hP : 1<10*μ.real (B.P j) := by
      unfold ActiveBank.q smaller10 at hq
      linarith [min_le_left (μ.real (B.P j)) (μ.real (B.Q j))]
    have hQ : 1<10*μ.real (B.Q j) := by
      unfold ActiveBank.q smaller10 at hq
      linarith [min_le_right (μ.real (B.P j)) (μ.real (B.Q j))]
    have hEx : 2+10*μ.real (Aᶜ\⋃ i,B.P i∪B.Q i) <
        10*μ.real (B.P j)+10*μ.real (B.Q j) := by
      unfold ActiveBank.h isolate10 ActiveBank.p ActiveBank.q larger10 smaller10 at hpivot
      linarith [max_add_min (μ.real (B.P j)) (μ.real (B.Q j))]
    obtain ⟨H,hH⟩ := strict_dominant_saturated μ K A Aᶜ hA hA.compl disjoint_compl_right
      hAm hout (zero_rectangle_restrict_lift μ A A hA hA subset_rfl K (hZero.mono (fun _ hz _ _=>hz)))
      B.P B.Q B.R mp mq (fun j=>(B.meas j).2.2) B.inside B.inner B.outer B.edge
      (fun j => (B.profiles j).imp id (fun ⟨_,_,h1,h2,_,_,rP,rQ⟩ => ⟨h1,h2,rP,rQ⟩))
      j hP hQ (by linarith [hJ.1]) (by linarith [hJ.2]) hEx
    exact (not_lt_of_ge (hb.trans (csInf_le (range_bdd μ K) ⟨H,rfl⟩))) hH
  · rcases hs with ⟨h3,hi⟩ | ⟨h2,hi⟩
    · exact Or.inr (B.petersen_of_unit hA hAm hμ hZero hb s h3 hi)
    · exact (B.two_large_light_bad hA hAm hZero hb s h2 hi).elim
  · exact (B.two_heavy_bad hA hAm hZero hb i j ne hi hj hh _ hL hrest).elim

#print axioms ActiveBank.classify
end SparseHalfGraphon
