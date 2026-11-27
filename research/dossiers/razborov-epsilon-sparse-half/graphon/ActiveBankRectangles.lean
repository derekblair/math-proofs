import ActiveBankModel

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
variable {K : Kernel Y} {A : Set Y} {I : Type*} (B : ActiveBank μ K A I)

def ActiveBank.side (j : I) (b : Bool) : Set Y := if b then B.Q j else B.P j
def ActiveBank.anchorSide (j : I) (b : Bool) : Set Y := if b then (B.R j)ᶜ else B.R j

lemma ActiveBank.side_meas (j : I) (b : Bool) : MeasurableSet (B.side j b) := by
  cases b
  · exact (B.meas j).1
  · exact (B.meas j).2.1

lemma ActiveBank.side_sub (j : I) (b : Bool) : B.side j b⊆B.P j∪B.Q j := by
  cases b
  · exact subset_union_left
  · exact subset_union_right

lemma ActiveBank.side_disj : Pairwise (fun u v : I×Bool => Disjoint (B.side u.1 u.2) (B.side v.1 v.2)) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  by_cases he : i=j
  · subst j
    have bc : b≠c := fun eq => h (by rw [eq])
    cases b <;> cases c
    · exact (bc rfl).elim
    · exact B.inner i
    · exact (B.inner i).symm
    · exact (bc rfl).elim
  · exact (B.outer he).mono (B.side_sub i b) (B.side_sub j c)

lemma ActiveBank.cross_rect (j : I) (b : Bool) :
    ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (B.side j b)),
      K.W z=(B.anchorSide j b).indicator (fun _ => (1:ℝ)) z.1 := by
  have hsub := (B.side_sub j b).trans (B.inside j)
  have hrel : (μ.restrict Aᶜ).restrict (B.side j b)=μ.restrict (B.side j b) :=
    Measure.restrict_restrict_of_subset hsub
  rcases B.profiles j with ⟨hP,hQ⟩ | ⟨_,_,_,_,hP,hQ,_,_⟩
  · cases b <;> simp [ActiveBank.side,hP,hQ]
  have H : ∀ᵐ v ∂μ.restrict A, ∀ᵐ x ∂(μ.restrict Aᶜ).restrict (B.side j b),
      K.W (v,x)=(B.anchorSide j b).indicator (fun _ => (1:ℝ)) v := by
    cases b
    · exact hP
    · exact hQ
  rw [hrel] at H
  have HM : MeasurableSet (B.anchorSide j b) := by
    cases b
    · exact (B.meas j).2.2
    · exact (B.meas j).2.2.compl
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun K.measurable_W
    ((measurable_const.indicator HM).comp measurable_fst))).mpr H

lemma ActiveBank.anchor_half (j : I) (hP : 0 < μ.real (B.P j))
    (hm : μ.real A=2/5) : (μ.restrict A).real (B.R j)=1/5 := by
  rcases B.profiles j with ⟨he,_⟩ | ⟨_,_,hh,_⟩
  · simp [he] at hP
  · rw [hh]
    norm_num [mass,hm]

lemma ActiveBank.outside_zero (i j : I) (b c : Bool) (h : i=j → b=c) :
    ∀ᵐ z ∂(μ.restrict (B.side i b)).prod (μ.restrict (B.side j c)), K.W z=0 := by
  have hi := (B.side_sub i b).trans (B.inside i)
  have hj := (B.side_sub j c).trans (B.inside j)
  have ha := (Measure.prod_mono (Measure.restrict_mono (μ:=μ) hi le_rfl) (Measure.restrict_mono (μ:=μ) hj le_rfl)).absolutelyContinuous
  have he := B.edge.filter_mono ha.ae_le
  have hm : ∀ᵐ z ∂(μ.restrict (B.side i b)).prod (μ.restrict (B.side j c)),
      z.1∈B.side i b ∧ z.2∈B.side j c := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem ((B.side_meas i b).prod (B.side_meas j c))
  filter_upwards [he,hm] with z hz hmem
  by_contra h0
  obtain ⟨k,e⟩ := hz (lt_of_le_of_ne (K.nonneg _) (Ne.symm h0))
  have unique {x : Y} {i j : I} {b c : Bool}
      (hx:x∈B.side i b) (hy:x∈B.side j c) : (i,b)=(j,c) := by
    by_contra hn
    exact Set.disjoint_left.mp (B.side_disj hn) hx hy
  rcases e with ⟨hP,hQ⟩ | ⟨hQ,hP⟩
  · have H := unique hmem.1 (show z.1∈B.side k false from hP)
    have J := unique hmem.2 (show z.2∈B.side k true from hQ)
    have bc := h (((congrArg Prod.fst H)).trans ((congrArg Prod.fst J).symm))
    have hb : b=false := congrArg Prod.snd H
    have hc : c=true := congrArg Prod.snd J
    rw [hb,hc] at bc
    contradiction
  · have H := unique hmem.1 (show z.1∈B.side k true from hQ)
    have J := unique hmem.2 (show z.2∈B.side k false from hP)
    have bc := h (((congrArg Prod.fst H)).trans ((congrArg Prod.fst J).symm))
    have hb : b=true := congrArg Prod.snd H
    have hc : c=false := congrArg Prod.snd J
    rw [hb,hc] at bc
    contradiction

#print axioms ActiveBank.cross_rect
#print axioms ActiveBank.outside_zero
end SparseHalfGraphon
