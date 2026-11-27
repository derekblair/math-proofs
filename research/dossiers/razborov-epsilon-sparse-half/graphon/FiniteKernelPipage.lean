import FiniteKernelPipageAlgebra
open scoped BigOperators
namespace SparseHalfGraphon
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def fractionalVertices (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => 0 < x v ∧ x v < 1)

theorem pipage_step (A : V → V → ℝ)
    (sym : ∀ u v, A u v=A v u) (diag : ∀ v, A v v=0) (nn : ∀ u v, 0≤A u v)
    (x : V → ℝ) (cap : ∀ v, 0≤x v ∧ x v≤1)
    (i j : V) (hij : i≠j) (hi : i ∈ fractionalVertices x) (hj : j∈fractionalVertices x) :
    ∃ y : V → ℝ, (∀ v, 0≤y v ∧ y v≤1) ∧ (∑ v,y v) = (∑ v,x v) ∧
      form A y y≤form A x x ∧ fractionalVertices y ⊂ fractionalVertices x := by
  let tp := min (1-x i) (x j)
  let tn := min (x i) (1-x j)
  have hp : 0≤tp := le_min (sub_nonneg.mpr (cap i).2) (cap j).1
  have hn : 0≤tn := le_min (cap i).1 (sub_nonneg.mpr (cap j).2)
  obtain ⟨t,ht,cost⟩ := favorable_shift A sym diag nn x i j tp tn hp hn
  let y (v : V) := x v+t*direction i j v
  have yi : y i=x i+t := by simp [y,direction_self i j hij]
  have yj : y j=x j-t := by simp [y,direction_other i j hij,sub_eq_add_neg]
  have yz (v : V) (h1 : v≠i) (h2 : v≠j) : y v=x v := by
    simp [y,direction_zero i j v h1 h2]
  have mass : (∑ v,y v) = ∑ v,x v := by
    simp [y,Finset.sum_add_distrib,← Finset.mul_sum,direction_sum]
  have hb_i : 0≤y i ∧ y i≤1 := by
    rw [yi]
    rcases ht with rfl | rfl
    · have hm := min_le_left (1-x i) (x j)
      change tp ≤ 1-x i at hm
      exact ⟨add_nonneg (cap i).1 hp,by linarith⟩
    · have hm := min_le_left (x i) (1-x j)
      change tn ≤ x i at hm
      constructor <;> linarith [(cap i).2]
  have hb_j : 0≤y j ∧ y j≤1 := by
    rw [yj]
    rcases ht with rfl | rfl
    · have hm := min_le_right (1-x i) (x j)
      change tp ≤ x j at hm
      constructor <;> linarith [(cap j).2]
    · have hm := min_le_right (x i) (1-x j)
      change tn ≤ 1-x j at hm
      constructor <;> linarith [(cap j).1]
  have capped (v : V) : 0≤y v ∧ y v≤1 := by
    by_cases h1 : v=i
    · simpa [h1] using hb_i
    by_cases h2 : v=j
    · simpa [h2] using hb_j
    · rw [yz v h1 h2]
      exact cap v
  have sub : fractionalVertices y ⊆ fractionalVertices x := by
    intro v hv
    by_cases h1 : v=i
    · simpa [h1] using hi
    by_cases h2 : v=j
    · simpa [h2] using hj
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have H := (Finset.mem_filter.mp hv).2
      rw [yz v h1 h2] at H
      exact H
  have hEdge (v : V) (hv : y v=0 ∨ y v=1) :
      v ∉ fractionalVertices y := by
    intro h
    obtain ⟨h1,h2⟩ := (Finset.mem_filter.mp h).2
    rcases hv with hv|hv <;> linarith
  have strict : ¬ fractionalVertices x ⊆ fractionalVertices y := by
    intro H
    rcases ht with rfl | rfl
    · by_cases h : 1-x i ≤ x j
      · have eq : tp=1-x i := min_eq_left h
        exact hEdge i (Or.inr (by rw [yi,eq]; ring)) (H hi)
      · have eq : tp=x j := min_eq_right (le_of_not_ge h)
        exact hEdge j (Or.inl (by rw [yj,eq]; ring)) (H hj)
    · by_cases h : x i ≤ 1-x j
      · have eq : tn=x i := min_eq_left h
        exact hEdge i (Or.inl (by rw [yi,eq]; ring)) (H hi)
      · have eq : tn=1-x j := min_eq_right (le_of_not_ge h)
        exact hEdge j (Or.inr (by rw [yj,eq]; ring)) (H hj)
  exact ⟨y,capped,mass,cost,ssubset_iff_subset_not_subset.mpr ⟨sub,strict⟩⟩

theorem pipage_one_fractional (A : V → V → ℝ)
    (sym : ∀ u v, A u v=A v u) (diag : ∀ v, A v v=0) (nn : ∀ u v, 0≤A u v)
    (x : V → ℝ) (cap : ∀ v, 0≤x v ∧ x v≤1) :
    ∃ y : V → ℝ, (∀ v, 0≤y v ∧ y v≤1) ∧
      (∑ v,y v) = (∑ v,x v) ∧ form A y y≤form A x x ∧ (fractionalVertices y).card ≤ 1 := by
  classical
  generalize hk : (fractionalVertices x).card = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases h : k≤1
    · exact ⟨x,cap,rfl,le_rfl,hk ▸ h⟩
    · have h1 : 1 < (fractionalVertices x).card := hk ▸ Nat.lt_of_not_ge h
      obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp h1
      obtain ⟨y,cy,my,fy,fy'⟩ := pipage_step A sym diag nn x cap i j hij hi hj
      have lower : (fractionalVertices y).card < k := hk ▸ Finset.card_lt_card fy'
      obtain ⟨z,cz,mz,fz,hz⟩ := ih _ lower y cy rfl
      exact ⟨z,cz,mz.trans my,fz.trans fy,hz⟩

#print axioms pipage_one_fractional
end SparseHalfGraphon
