import GeometricCapCount
import GeometricPairMoment

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal BigOperators
variable {J S : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace S]

theorem retained_below_half_mean (σ : Measure S) [IsProbabilityMeasure σ]
    (A : Set S) (Am : MeasurableSet A) (mpos : 0<(Fintype.card J:ℝ)*σ.real A) :
    let μ := Measure.pi (fun _ : J => σ)
    let M := (Fintype.card J:ℝ)*σ.real A
    μ.real {x : J→S | ((retained A x).card:ℝ)<M/2} ≤ 4/M := by
  classical
  intro μ M
  let p := σ.real A
  let I := fun i : J => fun x : J→S => A.indicator (fun _ => (1:ℝ)) (x i)
  let C := fun x : J→S => ((retained A x).card:ℝ)
  have Is (i : J) : Measurable (I i) := (measurable_const.indicator Am).comp (measurable_pi_apply i)
  have Ip (i : J) (x : J→S) : 0≤I i x := indicator_nonneg (fun _ _ => zero_le_one) _
  have Ib (i : J) (x : J→S) : ‖I i x‖≤1 := by
    by_cases h : x i∈A <;> simp [I,h]
  have II (i : J) : Integrable (I i) μ :=
    Integrable.of_bound (Is i).aestronglyMeasurable 1 (ae_of_all μ (Ib i))
  have JI (i j : J) : Integrable (fun x => I i x*I j x) μ := by
    apply Integrable.of_bound ((Is i).mul (Is j)).aestronglyMeasurable 1
    apply ae_of_all
    intro x
    change ‖I i x*I j x‖≤1
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (Ib i x) (Ib j x) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have CE (x : J→S) : C x=∑ i,I i x := by
    unfold C I
    simp only [Set.indicator]
    rw [←Finset.sum_filter]
    simp [retained]
  have IE (i : J) : (∫ x,I i x ∂μ)=p := by
    have f := measurePreserving_eval (fun _ : J => σ) i
    have h := integral_map (μ:=μ) f.measurable.aemeasurable (measurable_const.indicator (f:=fun _ : S => (1:ℝ)) Am).aestronglyMeasurable
    rw [f.map_eq] at h
    change _=(∫ x,I i x ∂μ) at h
    rw [←h,integral_indicator Am,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
    rfl
  have JE (i j : J) : (∫ x,I i x*I j x ∂μ)=if i=j then p else p^2 := by
    by_cases e : i=j
    · subst j
      rw [ite_eq_left rfl,←IE i]
      congr 1
      funext x
      by_cases h : x i∈A <;> simp [I,h]
    · rw [ite_eq_right e]
      have f := distinct_pair_marginal σ i j e
      let g := A.indicator (fun _ => (1:ℝ))
      have gm : Measurable g := measurable_const.indicator Am
      have h := integral_map (μ:=μ) f.measurable.aemeasurable
        (((gm.comp measurable_fst).mul (gm.comp measurable_snd))).aestronglyMeasurable
      rw [f.map_eq] at h
      change (∫ z : S×S, g z.1*g z.2 ∂(σ.prod σ))=(∫ x,I i x*I j x ∂μ) at h
      rw [←h,integral_prod_mul g g]
      unfold g
      rw [integral_indicator Am,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,pow_two]
      rfl
  have CI : Integrable C μ := by
    rw [show C=(fun x => ∑ i,I i x) from funext CE]
    exact integrable_finsetSum _ (fun i _ => II i)
  have C2I : Integrable (fun x => (C x)^2) μ := by
    simp_rw [CE,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => JI i j))
  have cE : (∫ x,C x ∂μ)=M := by
    simp_rw [CE]
    rw [integral_finsetSum _ (fun i _ => II i)]
    simp [IE,M,p,nsmul_eq_mul]
  have c2E : (∫ x,(C x)^2 ∂μ)=M+(Fintype.card J:ℝ)*((Fintype.card J:ℝ)-1)*p^2 := by
    simp_rw [CE,pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => JI i j))]
    simp_rw [integral_finsetSum _ (fun j _ => JI _ j),JE]
    have h (i : J) : (∑ j, if i=j then p else p^2)=p+((Fintype.card J:ℝ)-1)*p^2 := by
      rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have z (j : J) (hj : j∈(Finset.univ : Finset J).erase i) : (if i=j then p else p^2)=p^2 :=
        ite_eq_right (Ne.symm (Finset.mem_erase.1 hj).1)
      rw [Finset.sum_congr rfl z, ite_eq_left rfl, Finset.sum_const,nsmul_eq_mul,
        Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,
        Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i⟩)]
      push_cast
      ring
    simp_rw [h]
    rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    dsimp [M,p]
    ring
  let F := fun x : J→S => (C x-M)^2
  have FI : Integrable F μ := by
    simp_rw [F,show ∀ x : ℝ,(x-M)^2=x^2-2*M*x+M^2 by intro x; ring]
    exact (C2I.sub (CI.const_mul (2*M))).add (integrable_const _)
  have FE : (∫ x,F x ∂μ)≤M := by
    simp_rw [F,show ∀ x : ℝ,(x-M)^2=x^2-2*M*x+M^2 by intro x; ring]
    change (∫ x, ((fun y => C y^2) - fun y => (2*M)*C y) x + M^2 ∂μ)≤_
    rw [integral_add (C2I.sub (CI.const_mul (2*M))) (integrable_const _)]
    simp only [Pi.sub_apply]
    rw [integral_sub C2I (CI.const_mul _),integral_const_mul,integral_const,cE,c2E]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul]
    change M+(Fintype.card J:ℝ)*((Fintype.card J:ℝ)-1)*p^2-2*M*M+M^2≤M
    have zz : 0≤(Fintype.card J:ℝ)*p^2 := by positivity
    dsimp [M]
    change _ ≤ (Fintype.card J:ℝ)*p
    nlinarith only [zz]
  let D := (M/2)^2
  have Dp : 0<D := by dsimp [D]; positivity
  have sub : {x | C x<M/2}⊆{x | D≤F x} := by
    intro x h
    change C x<M/2 at h
    change (M/2)^2≤(C x-M)^2
    have hh : M/2≤M-C x := by linarith only [h]
    rw [show C x-M=-(M-C x) by ring,neg_sq]
    exact pow_le_pow_left₀ (by positivity) hh 2
  have mr := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (μ:=μ) sub)
  have m := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (fun x => sq_nonneg (C x-M))) FI D
  have z := (mul_le_mul_of_nonneg_left mr Dp.le).trans (m.trans FE)
  have b : μ.real {x | C x<M/2} ≤ M/D := (le_div_iff₀ Dp).2 (by rw [mul_comm]; exact z)
  refine b.trans_eq ?_
  dsimp [D]
  field_simp
  ring

#print axioms retained_below_half_mean
end RobustFolkman.GeometricGap
