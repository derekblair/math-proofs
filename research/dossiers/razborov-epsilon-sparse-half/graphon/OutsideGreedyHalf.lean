import OutsideAllocation
import GreedyHalf
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
open SparseHalfCountableEndpoint
variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def side10 (P : I→Set X) (i : I) : ℝ := 10*μ.real (P i)
noncomputable def isolate10 (S : Set X) (P Q : I→Set X) : ℝ :=
  10*μ.real (S\⋃ i,P i∪Q i)

/-- Translate the countable numerical greedy half to an actual fractional
half of the graphon. Work only on the outside and do not complete any edge. -/
theorem outside_greedy_half_oriented (K : Kernel X) (S : Set X) (ms : MeasurableSet S) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i))
    (edge : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<K.W z → ∃ i,
      (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (ordered : ∀ i, μ.real (Q i)≤μ.real (P i)) (cap : ∀ i, μ.real (P i)≤1/5)
    (size : μ.real S=3/5) :
    (5 ≤ isolate10 μ S P Q+(∑' i, side10 μ P i) ∧
      ∃ H : Half μ,(∀ x∉S,H.f x=0) ∧ halfEnergy μ K H≤0) ∨
    ∃ θ : ℝ, 0≤θ ∧ θ≤2 ∧
      ∃ H : Half μ,(∀ x∉S,H.f x=0) ∧
        halfEnergy μ K H≤dual (side10 μ P) (side10 μ Q) θ /100 := by
  let L := ⋃ i,P i∪Q i
  let R := S\L
  let p := side10 μ P
  let q := side10 μ Q
  let h := isolate10 μ S P Q
  have eP (i) : p i=10*μ.real (P i) := rfl
  have eQ (i) : q i=10*μ.real (Q i) := rfl
  have eH : h=10*μ.real R := rfl
  have pm (i) : 0≤p i := by rw [eP]; positivity
  have qm (i) : 0≤q i := by rw [eQ]; positivity
  have up (i) : p i≤2 := by rw [eP]; linarith [cap i]
  have qp (i) : q i≤p i := by rw [eQ,eP]; linarith [ordered i]
  have h0 : 0≤h := by rw [eH]; positivity
  have cm (i) : MeasurableSet (P i∪Q i) := (mp i).union (mq i)
  have lm : MeasurableSet L := MeasurableSet.iUnion cm
  have ls : L⊆S := iUnion_subset inside
  have C := real_mass_hasSum μ (fun i=>P i∪Q i) cm outer
  have cs (i) : p i+q i=10*μ.real (P i∪Q i) := by
    rw [eP,eQ,measureReal_union (inner i) (mq i),mul_add]
  have ss : Summable (fun i=>p i+q i) := by
    simp_rw [cs]
    exact C.summable.mul_left 10
  have sp := Summable.of_nonneg_of_le pm (fun i=>le_add_of_nonneg_right (qm i)) ss
  have sq := Summable.of_nonneg_of_le qm (fun i=>le_add_of_nonneg_left (pm i)) ss
  have bank : (∑' i, (p i+q i)) + h = 6 := by
    simp_rw [cs]
    rw [C.summable.tsum_mul_left,C.tsum_eq,eH,measureReal_sdiff ls lm,size]
    try ring
  rcases greedy_half p q h ss up qm qp bank with free|⟨θ,k,t0,t2,k0,k1,x,shape,feas,full,cost,best⟩
  · left
    refine ⟨free,?_⟩
    let F := h+(∑' i,p i)
    let t := 5/F
    have fpos : 0<F := lt_of_lt_of_le (by norm_num) free
    have t0 : 0≤t := div_nonneg (by norm_num) fpos.le
    have t1 : t≤1 := (div_le_iff₀ fpos).mpr (by simpa using free)
    have A (i) : 0≤t*(p i/10) := mul_nonneg t0 (div_nonneg (pm i) (by norm_num))
    have A' (i) : t*(p i/10)≤μ.real (P i) := by
      rw [eP]; ring_nf
      simpa using mul_le_mul_of_nonneg_right t1 (measureReal_nonneg (μ:=μ) (s:=P i))
    have hr : t*(h/10)≤μ.real R := by
      rw [eH]; ring_nf
      simpa using mul_le_mul_of_nonneg_right t1 (measureReal_nonneg (μ:=μ) (s:=R))
    obtain ⟨D,dm,du,dz,massD,energy⟩ := outside_pair_allocation μ K S ms P Q mp mq inside inner outer edge
      (fun i=>t*(p i/10)) (fun _=>0) A (fun _=>le_rfl) A' (fun _=>measureReal_nonneg)
      (t*(h/10)) (mul_nonneg t0 (div_nonneg h0 (by norm_num))) hr
    have massD' : (∫ x,D x ∂μ)=1/2 := by
      rw [massD,(sp.div_const 10).tsum_mul_left,tsum_div_const,tsum_zero,add_zero]
      have e : t*F=5 := div_mul_cancel₀ _ fpos.ne'
      dsimp [F] at e
      linarith [show t*(h/10)+t*((∑' i,p i)/10)=t*(h+(∑' i,p i))/10 by ring]
    exact ⟨⟨D,dm.1,fun x=>(du x).1,fun x=>(du x).2,massD'⟩,dz,by simpa [halfEnergy] using energy⟩
  · right
    have xp (i) : x i/10≤μ.real (Q i) := by have f := (feas i).2; rw [eQ] at f; linarith
    have sx := Summable.of_nonneg_of_le (fun i=>(feas i).1) (fun i=>(feas i).2) sq
    obtain ⟨D,dm,du,dz,massD,energy⟩ := outside_pair_allocation μ K S ms P Q mp mq inside inner outer edge
      (fun i=>p i/10) (fun i=>x i/10) (fun i=>div_nonneg (pm i) (by norm_num))
      (fun i=>div_nonneg (feas i).1 (by norm_num))
      (fun i=>by rw [eP]; ring_nf; rfl) xp
      (h/10) (div_nonneg h0 (by norm_num)) (by rw [eH]; ring_nf; rfl)
    have massD' : (∫ x,D x ∂μ)=1/2 := by
      rw [massD,tsum_div_const,tsum_div_const]
      linarith
    let H : Half μ := ⟨D,dm.1,fun x=>(du x).1,fun x=>(du x).2,massD'⟩
    refine ⟨θ,t0,t2,H,dz,?_⟩
    change (∫ y,(∫ x,K.W (x,y)*D x ∂μ)*D y ∂μ)/2 ≤ _
    have eq (i : I) : (p i/10)*(x i/10)=p i*x i/100 := by ring
    simp_rw [eq,tsum_div_const,cost] at energy
    exact energy

/-- If actual beta is at least 1/50, free mass is impossible and the
numerical greedy dual of the oriented paired bank reaches normalized cost 2. -/
theorem outside_dual_ge_two (K : Kernel X) (S : Set X) (ms : MeasurableSet S) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i))
    (edge : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<K.W z → ∃ i,
      (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (ordered : ∀ i, μ.real (Q i)≤μ.real (P i)) (cap : ∀ i, μ.real (P i)≤1/5)
    (size : μ.real S=3/5) (high : 1/50≤beta μ K) :
    ∃ θ : ℝ, 0≤θ ∧ θ≤2 ∧ 2≤dual (side10 μ P) (side10 μ Q) θ := by
  have cost_ge (H : Half μ) : 1/50≤halfEnergy μ K H :=
    high.trans (csInf_le (range_bdd μ K) ⟨H,rfl⟩)
  rcases outside_greedy_half_oriented μ K S ms P Q mp mq inside inner outer edge ordered cap size
    with ⟨_,H,_,z⟩|⟨θ,θ0,θ2,H,_,h⟩
  · linarith [cost_ge H]
  · exact ⟨θ,θ0,θ2,by linarith [cost_ge H]⟩

#print axioms outside_greedy_half_oriented
#print axioms outside_dual_ge_two
end SparseHalfGraphon
