import ProfileCodes

open MeasureTheory Set Function
namespace SparseHalfGraphon
variable {X : Type*} [mx : MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

lemma profile_real_cell (K : Kernel X) (x:X) (S:Set X) (hS:MeasurableSet S) :
    (reweight ν (fun y=>K.W (x,y))).real S=deg (ν.restrict S) K x := by
  have h₀ : ∀ yy : X, 0≤K.W (x,yy) := fun _ => K.nonneg _
  have he := reweight_mass (ν.restrict S) (fun y=>K.W (x,y))
    (rowMeasurable K x) h₀
  unfold reweight at he
  rw [← restrict_withDensity hS] at he
  change mass ((reweight ν (fun y=>K.W (x,y))).restrict S)=_ at he
  simpa only [mass,measureReal_restrict_apply_univ,deg] using he

/-- On a countably generated anchor space, profile codes have exactly the
same fibers as rows modulo almost-everywhere equality. -/
theorem profile_code_injective_ae (T:ℕ→Set X) (K:Kernel X)
    (hm : ∀ n, MeasurableSet (T n))
    (hg : mx=MeasurableSpace.generateFrom (range T))
    (hpi : IsPiSystem (range T)) (hu : univ∈range T)
    (x y:X) (he : profileCode ν T K x=profileCode ν T K y) :
    (fun z=>K.W (x,z))=ᵐ[ν](fun z=>K.W (y,z)) := by
  let a:=reweight ν (fun z=>K.W (x,z))
  let b:=reweight ν (fun z=>K.W (y,z))
  have : IsFiniteMeasure a := isFiniteMeasure_of_le ν (reweight_le ν _ (fun _ => K.le_one _))
  have : IsFiniteMeasure b := isFiniteMeasure_of_le ν (reweight_le ν _ (fun _ => K.le_one _))
  have hab : a=b := by
    apply Measure.ext_of_generateFrom_of_iUnion (range T) (fun _ => univ) hg hpi
      (by ext z; simp) (fun _=>hu) (fun _=>measure_ne_top a _)
    rintro S ⟨n,rfl⟩
    have hh := congrFun he n
    change deg (ν.restrict (T n)) K x=deg (ν.restrict (T n)) K y at hh
    calc
      a (T n)=ENNReal.ofReal (a.real (T n)) := (ENNReal.ofReal_toReal (measure_ne_top a _)).symm
      _=ENNReal.ofReal (b.real (T n)) := by
        congr 1
        exact (profile_real_cell ν K x (T n) (hm n)).trans
          (hh.trans (profile_real_cell ν K y (T n) (hm n)).symm)
      _=b (T n) := ENNReal.ofReal_toReal (measure_ne_top b _)
  have ha := Measure.rnDeriv_withDensity ν (rowMeasurable K x).ennreal_ofReal
  have hb := Measure.rnDeriv_withDensity ν (rowMeasurable K y).ennreal_ofReal
  change a.rnDeriv ν =ᵐ[ν] (fun z=>ENNReal.ofReal (K.W (x,z))) at ha
  change b.rnDeriv ν =ᵐ[ν] (fun z=>ENNReal.ofReal (K.W (y,z))) at hb
  rw [hab] at ha
  filter_upwards [ha.symm.trans hb] with z hz
  have h := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal (K.nonneg _)] using h

#print axioms profile_code_injective_ae
end SparseHalfGraphon
