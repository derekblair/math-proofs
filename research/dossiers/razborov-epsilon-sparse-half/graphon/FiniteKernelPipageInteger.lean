import FiniteKernelPipage
open scoped BigOperators
namespace SparseHalfGraphon
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def oneVertices (y : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => y v=1)

noncomputable def alloc (s : Finset V) (v : V) : ℝ := if v ∈ s then 1 else 0

theorem sum_alloc (s : Finset V) : ∑ v, alloc s v = s.card := by
  unfold alloc
  have h : (Finset.univ.filter (fun v => v ∈ s)) = s := by ext; simp
  simp only [← Finset.sum_filter,h,Finset.sum_const,nsmul_eq_mul,mul_one]

theorem pipage_integer (A : V → V → ℝ)
    (sym : ∀ u v, A u v=A v u) (diag : ∀ v, A v v=0) (nn : ∀ u v, 0≤A u v)
    (x : V → ℝ) (cap : ∀ v, 0≤x v ∧ x v≤1) (m : ℕ) (mass : ∑ v,x v = m) :
    ∃ s : Finset V, s.card = m ∧ form A (alloc s) (alloc s) ≤ form A x x := by
  classical
  obtain ⟨y,cy,my,fy,hy⟩ := pipage_one_fractional A sym diag nn x cap
  let s := oneVertices y
  have endpoints (v : V) (hv : v ∉ fractionalVertices y) : y v=alloc s v := by
    by_cases h : y v=1
    · have hh : v ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
      simp [alloc,hh,h]
    · have hh : v ∉ s := fun hs => h (Finset.mem_filter.mp hs).2
      have hz : y v=0 := by
        by_contra h0
        have p : 0 < y v := lt_of_le_of_ne (cy v).1 (Ne.symm h0)
        have q : y v < 1 := lt_of_le_of_ne (cy v).2 h
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,q⟩)
      simp [alloc,hh,hz]
  have none (v : V) : v ∉ fractionalVertices y := by
    intro h
    have h' (w : V) (hn : w ≠ v) : w ∉ fractionalVertices y := by
      intro H
      have ht := Finset.one_lt_card.mpr ⟨w,H,v,h,hn⟩
      omega
    have hv : 0<y v ∧ y v<1 := (Finset.mem_filter.mp h).2
    have hn : v ∉ s := fun hs => by linarith [(Finset.mem_filter.mp hs).2,hv.2]
    have E (w : V) : y w = alloc s w+(if w=v then y v else 0) := by
      by_cases ew : w=v
      · subst w
        simp [alloc,hn]
      · simp [ew,endpoints w (h' w ew)]
    have he := my.trans mass
    rw [Finset.sum_congr rfl (fun w _ => E w)] at he
    simp only [Finset.sum_add_distrib,sum_alloc,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
    have lo : s.card < m := by exact_mod_cast (show (s.card : ℝ) < (m:ℝ) by linarith [hv.1])
    have hi : m < s.card+1 := by exact_mod_cast (show (m : ℝ) < (s.card : ℝ)+1 by linarith [hv.2])
    omega
  have eq : y = alloc s := funext (fun v => endpoints v (none v))
  refine ⟨s,?_ ,?_⟩
  · rw [eq,sum_alloc] at my
    exact_mod_cast my.trans mass
  · simpa only [eq] using fy

#print axioms pipage_integer
end SparseHalfGraphon
