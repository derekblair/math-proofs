import FiniteGreedyKernelBridge
import GreedyEligible
import LowerMarkLimit

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq V]

/-- Loss and the nearly stopped greedy set on an actual finite graph. -/
theorem finite_greedy_reduction
    (G : V→V→Bool) (sym : ∀ u v,G u v=G v u) (loop : ∀ v,G v v=false)
    (tf : ∀ u v w,G u v=true → G u w=true → G v w=false)
    (m : ℕ) (hn : Fintype.card V=2*m) (hp : 0<Fintype.card V)
    (A : Finset V) (hInd : IndependentCells G (A:Set V))
    (a : ℝ) (ha : a=(A.card:ℝ)/(Fintype.card V:ℝ))
    (ha0 : 39/100≤a)
    (hcap : ∀ s : Finset V, IndependentCells G (s:Set V) →
      (s.card:ℝ)/(Fintype.card V:ℝ)≤a)
    (hBad : 1/50<beta uniformVertices (adjacencyKernel G sym)) :
    ∃ B : Finset V, A⊆B ∧
      (∀ x∉B, 1/2-a≤deg (uniformVertices.restrict (B:Set V)) (adjacencyKernel G sym) x) ∧
      a ≤ (uniformVertices : Measure V).real (B:Set V) ∧
      (uniformVertices : Measure V).real (B:Set V)≤1/2 ∧
      1/50+(3/100)*((uniformVertices : Measure V).real (B:Set V)-a)<a*(1/2-a)/2 := by
  let μ : Measure V := uniformVertices
  let W := adjacencyKernel G sym
  let n : ℝ := Fintype.card V
  have n0 : 0<n := by dsimp [n]; exact_mod_cast hp
  have hm : (m:ℝ)/n=1/2 := by
    have hh : n=2*(m:ℝ) := by dsimp [n]; exact_mod_cast hn
    apply (div_eq_iff n0.ne').mpr
    linarith
  have hmμ : mass μ=1 := uniform_mass hp
  have hAm : μ.real (A:Set V)=a := (uniform_finset A).trans ha.symm
  have hAm' : a<1/2 := by
    by_contra! hb
    have h := zero_supported_half μ W (A:Set V) A.finite_toSet.measurableSet (hAm.symm ▸ hb)
      (ae_of_all _ (fun z hx hy=>by
        change edgeReal (G z.1 z.2)=0
        simp [edgeReal,hInd z.1 hx z.2 hy]))
    linarith [hBad]
  have haN : A.card≤m := by
    have h := div_lt_div_iff_of_pos_right n0 |>.mp (show (A.card:ℝ)/n<(m:ℝ)/n by rwa [hm,←ha])
    exact_mod_cast h.le
  let C (u v : V) := W.W (u,v)
  have hzero : unorderedCost C A=0 := by
    unfold unorderedCost
    have he : ∑ u∈A,∑ v∈A,C u v=0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      change edgeReal (G u v)=0
      simp [edgeReal,hInd u hu v hv]
    simp [he]
  obtain ⟨B,hAB,hBm,hBC,hBstop⟩ := finite_greedy_growth C W.symm
      (fun u=>by change edgeReal (G u u)=0; simp [edgeReal,loop u]) A hzero m haN ((1/2-a)*n)
  let b := μ.real (B:Set V)
  have hB : b=(B.card:ℝ)/n := uniform_finset B
  have hab : a≤b := by
    rw [← hAm]
    exact measureReal_mono (show (A:Set V)⊆(B:Set V) from hAB)
  have hb : b≤1/2 := by
    rw [hB,←hm]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hBm) n0.le
  have hcost : energyPair μ W (indicatorWeight (B:Set V)) (indicatorWeight (B:Set V))/2≤(1/2-a)*(b-a) := by
    rw [uniform_mark_cost]
    change unorderedCost C B/n^2≤_
    have hh := div_le_div_of_nonneg_right hBC (sq_nonneg n)
    have hEq : ((1/2-a)*n*((B.card:ℝ)-(A.card:ℝ)))/n^2=(1/2-a)*(b-a) := by
      rw [hB,ha]
      change (1/2-(A.card:ℝ)/n)*n*((B.card:ℝ)-(A.card:ℝ))/n^2=_
      field_simp
      <;> ring
    exact hh.trans_eq hEq
  have hFloor : ∀ x∉B, 1/2-a≤deg (μ.restrict (B:Set V)) W x := by
    rcases hBstop with hx | hdeg
    · have hBhalf : b=1/2 := by rw [hB,hx,hm]
      have Hm := indicatorWeight_unit (B:Set V) B.finite_toSet.measurableSet
      let H : Half μ := ⟨indicatorWeight (B:Set V),Hm.1,fun x=>(Hm.2 x).1,
        fun x=>(Hm.2 x).2,(indicatorWeight_mass μ _ B.finite_toSet.measurableSet).trans hBhalf⟩
      have hc := csInf_le (range_bdd μ W) (show halfEnergy μ W H∈range (halfEnergy μ W) from ⟨H,rfl⟩)
      rw [halfEnergy_as_pair] at hc
      change beta μ W≤energyPair μ W (indicatorWeight (B:Set V)) (indicatorWeight (B:Set V))/2 at hc
      rw [hBhalf] at hcost
      have he := mul_nonneg (show 0≤1/2-a by linarith) (show 0≤a-39/100 by linarith)
      exfalso
      change 1/50<beta μ W at hBad
      nlinarith
    · intro x hx
      have hh := hdeg x hx
      rw [uniform_K_deg_finite_set]
      exact ((le_div_iff₀ n0).mpr hh.le)
  have hHigh := finite_highOutside_cap G sym tf (B:Set V) a hcap
  have hh := greedy_from_high_cap μ hmμ W (B:Set V) B.finite_toSet.measurableSet a ha0 hAm'
    hab hb hcost (adjacency_triangle_zero G sym tf) (fun x hx=>hFloor x hx) hHigh
  change 1/50<beta μ W at hBad
  exact ⟨B,hAB,hFloor,hab,hb,by linarith⟩

#print axioms finite_greedy_reduction
end SparseHalfGraphon
