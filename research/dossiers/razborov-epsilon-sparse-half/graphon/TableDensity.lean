import TableConsistency

open Filter Set Topology Function
namespace SparseHalfGraphon

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
variable {p : ∀ n, I (n+1) → I n}

noncomputable def CoherentTables.density (B : CoherentTables I p) (n : ℕ) (i j : I n) :=
  B.joint n i j / (B.cell n i * B.cell n j)

lemma CoherentTables.density_nonneg (B : CoherentTables I p) (n : ℕ) (i j : I n) :
    0 ≤ B.density n i j :=
  div_nonneg (B.joint_zero n i j) (mul_nonneg (B.cell_zero n i) (B.cell_zero n j))

lemma CoherentTables.density_le_one (B : CoherentTables I p) (n : ℕ) (i j : I n) :
    B.density n i j ≤ 1 := by
  unfold CoherentTables.density
  by_cases h : B.cell n i * B.cell n j = 0
  · simp [h]
  · apply (div_le_iff₀ (lt_of_le_of_ne (mul_nonneg (B.cell_zero n i)
      (B.cell_zero n j)) (Ne.symm h))).mpr
    simpa using B.joint_bound n i j

lemma CoherentTables.density_symm (B : CoherentTables I p) (n : ℕ) (i j : I n) :
    B.density n i j = B.density n j i := by
  unfold CoherentTables.density
  rw [B.joint_symm n i j, mul_comm]

/-- The density-times-area formula stays exact also on zero-size cells. -/
lemma CoherentTables.density_mul_area (B : CoherentTables I p) (n : ℕ) (i j : I n) :
    B.density n i j * (B.cell n i * B.cell n j) = B.joint n i j := by
  unfold CoherentTables.density
  by_cases h : B.cell n i * B.cell n j = 0
  · rw [h]
    have hz := B.joint_bound n i j
    rw [h] at hz
    simp [le_antisymm hz (B.joint_zero n i j)]
  · exact div_mul_cancel₀ _ h

/-- Only positive-size limit cells need density convergence. -/
theorem tendsto_table_density {P : ℕ → ∀ n, I (n+1) → I n}
    (A : ∀ k : ℕ, CoherentTables I (P k)) (B : CoherentTables I p) (n : ℕ) (i j : I n)
    (hi : 0 < B.cell n i) (hj : 0 < B.cell n j)
    (hCi : Tendsto (fun k => (A k).cell n i) atTop (𝓝 (B.cell n i)))
    (hCj : Tendsto (fun k => (A k).cell n j) atTop (𝓝 (B.cell n j)))
    (hJ : Tendsto (fun k => (A k).joint n i j) atTop (𝓝 (B.joint n i j))) :
    Tendsto (fun k => (A k).density n i j) atTop (𝓝 (B.density n i j)) :=
  hJ.div (hCi.mul hCj) (mul_ne_zero hi.ne' hj.ne')

#print axioms CoherentTables.density_mul_area
#print axioms tendsto_table_density
end SparseHalfGraphon
