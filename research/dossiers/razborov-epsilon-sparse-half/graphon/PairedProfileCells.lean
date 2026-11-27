import PairedFiberRows
import PairedOrbitSets
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [mx : MeasurableSpace X]
variable (ω ν : Measure X) [IsFiniteMeasure ω] [IsFiniteMeasure ν]

/-- Disjoint matching of all genuinely complementary atomic profile pairs.
Almost all outside edges lie across its pairs, and a typical anchor root
takes a complementary full/zero load on the sides of every pair. -/
theorem paired_profile_cells
    (K : Kernel X) (T : ℕ → Set X)
    (hm : ∀ n, MeasurableSet (T n)) (hg : mx=MeasurableSpace.generateFrom (range T))
    (hpi : IsPiSystem (range T)) (hu : univ∈range T)
    (nonnull : ν univ ≠ 0) (S : Set X) (ms : MeasurableSet S)
    (h : ∀ᵐ z ∂ω.prod ω, K.W z=0 ∨ ∀ᵐ v ∂ν, ComplementaryAt K z.1 z.2 v) :
    ∃ (I : Type) (_ : Countable I) (_ : Nonempty I) (P Q : I → Set X),
      (∀ i, MeasurableSet (P i)) ∧ (∀ i, MeasurableSet (Q i)) ∧
      (∀ i, P i ∪ Q i ⊆ S) ∧ (∀ i, Disjoint (P i) (Q i)) ∧
      Pairwise (Disjoint on fun i => P i ∪ Q i) ∧
      (∀ᵐ z ∂ω.prod ω, z.1∈S → z.2∈S → 0<K.W z →
        ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i)) ∧
      (∀ᵐ v ∂ν, PairedRow ω K P Q v) := by
  let p := profileCode ν T K
  let f := codeFlip ν T
  have pm : Measurable p := profileCode_meas ν T K
  have fm : Measurable f := codeFlip_meas ν T
  have fi : Involutive f := codeFlip_inv ν T
  let A : Set (ℕ→ℝ) := {a | a ∈ atomLabels ω p ∧ f a ∈ atomLabels ω p ∧
      ∃ x y, p x=a ∧ p y=f a ∧ ∀ᵐ v ∂ν, ComplementaryAt K x y v}
  have ac : A.Countable := (atomLabels_countable ω p pm).mono fun _ h => h.1
  have af (a) (ha : a∈A) : f a∈A := by
    obtain ⟨u,v,x,y,xe,ye,c⟩ := ha
    refine ⟨v,by simpa only [fi a] using u,y,x,ye,xe.trans (fi a).symm,?_⟩
    filter_upwards [c] with z hz
    exact complementaryAt_symm K x y z hz
  have an (a) (ha : a∈A) : f a≠a := by
    obtain ⟨_,_,x,y,xe,ye,c⟩ := ha
    intro E
    exact complementary_codes_distinct ν nonnull T K hm hg hpi hu x y c
      (xe.trans (ye.trans E).symm)
  obtain ⟨I,ic,ine,P,Q,mp,mq,inside,inner,outer,sh,edge⟩ :=
    orbit_pair_sets S ms p pm f fi A ac af an
  letI : Countable I := ic
  refine ⟨I,ic,ine,P,Q,mp,mq,inside,inner,outer,?_,?_⟩
  · have relm : MeasurableSet {z : X×X | p z.2=f (p z.1)} :=
      measurableSet_eq_fun (pm.comp measurable_snd) (fm.comp (pm.comp measurable_fst))
    have at2 := relation_on_atoms ω p pm f relm
    have at1 := (Measure.measurePreserving_swap (μ:=ω) (ν:=ω)).quasiMeasurePreserving.ae at2
    filter_upwards [h,at1,at2] with z hz ax ay xs ys positive
    rcases hz with zero|c
    · exact False.elim ((ne_of_gt positive) zero)
    · have E : p z.2=f (p z.1) := indicator_rows_codes ν T K z.1 z.2 c
      have E' : p z.1=f (p z.2) := by rw [E,fi]
      have ax' : p z.1=f (p z.2) → p z.1∈atomLabels ω p := ax
      exact edge _ xs _ ys ⟨ax' E',E ▸ ay E,z.1,z.2,rfl,E,c⟩ E
  · unfold PairedRow
    apply ae_all_iff.mpr
    intro i
    rcases sh i with ⟨emptyP,emptyQ⟩|⟨a,ha,eqP,eqQ⟩
    · simp [emptyP,emptyQ]
    · obtain ⟨_,_,x,y,xe,ye,c⟩ := ha
      have ip := integral_on_code_fiber ω ν T K hm hg hpi hu (P i) (mp i) x (by
        intro z hz
        rw [eqP] at hz
        exact (show p z=a from hz.2).trans xe.symm)
      have iq := integral_on_code_fiber ω ν T K hm hg hpi hu (Q i) (mq i) y (by
        intro z hz
        rw [eqQ] at hz
        exact (show p z=f a from hz.2).trans ye.symm)
      filter_upwards [ip,iq,c] with v hp hq hc
      rcases hc with ⟨c0,c1⟩|⟨c1,c0⟩
      · right
        simp [hp,hq,c0,c1]
      · left
        simp [hp,hq,c0,c1]

#print axioms paired_profile_cells
end SparseHalfGraphon
