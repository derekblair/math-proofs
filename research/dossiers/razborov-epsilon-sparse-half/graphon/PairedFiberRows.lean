import PairedDichotomy
import PairOrient
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [mx : MeasurableSpace X]
variable (ω ν : Measure X) [IsFiniteMeasure ω] [IsFiniteMeasure ν]

def ComplementaryAt (K : Kernel X) (x y v : X) : Prop :=
  (K.W (x,v)=0 ∧ K.W (y,v)=1) ∨ (K.W (x,v)=1 ∧ K.W (y,v)=0)

lemma complementaryAt_symm (K : Kernel X) (x y v : X) :
    ComplementaryAt K x y v → ComplementaryAt K y x v := by
  unfold ComplementaryAt
  tauto

/-- The profiles in a code fiber all equal the witness row almost everywhere on the
anchor. By Fubini, a typical anchor has that witness value across almost all the fiber. -/
theorem integral_on_code_fiber
    (T : ℕ → Set X) (K : Kernel X)
    (hm : ∀ n, MeasurableSet (T n)) (hg : mx=MeasurableSpace.generateFrom (range T))
    (hpi : IsPiSystem (range T)) (hu : univ∈range T)
    (B : Set X) (mb : MeasurableSet B) (w : X)
    (code : ∀ z∈B, profileCode ν T K z=profileCode ν T K w) :
    ∀ᵐ v ∂ν, (∫ z in B, K.W (v,z) ∂ω)=ω.real B*K.W (w,v) := by
  let p (z : X × X) : Prop := K.W z=K.W (w,z.2)
  have measurableP : MeasurableSet {z:X×X | p z} :=
    measurableSet_eq_fun K.measurable_W ((rowMeasurable K w).comp measurable_snd)
  have H : ∀ᵐ z ∂ω.restrict B, ∀ᵐ v ∂ν, p (z,v) := by
    filter_upwards [ae_restrict_mem mb (μ:=ω)] with z hz
    exact profile_code_injective_ae ν T K hm hg hpi hu z w (code z hz)
  have E := (Measure.ae_ae_comm measurableP).mp H
  filter_upwards [E] with v hv
  have hh : (fun z => K.W (v,z)) =ᵐ[ω.restrict B] (fun _ => K.W (w,v)) := by
    filter_upwards [hv] with z h
    exact (K.symm v z).trans h
  rw [integral_congr_ae hh,setIntegral_const,smul_eq_mul]

#print axioms integral_on_code_fiber
end SparseHalfGraphon
