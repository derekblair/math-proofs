import FiniteIntervalSplit
import TableDensity

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
variable {p : ∀ n, I (n+1) → I n}

namespace CoherentTables
variable (B : CoherentTables I p)

noncomputable def childLeft (n : ℕ) (a : ℝ) (i : I n) : {j // p n j = i} → ℝ :=
  (finite_interval_split a
      (fun j : {j // p n j = i} => B.cell (n+1) j.val)
      (fun j => B.cell_zero (n+1) j.val)).choose

lemma child_partition (n : ℕ) (a : ℝ) (i : I n) :
    (⋃ j : {j // p n j = i},
      Ico (B.childLeft n a i j) (B.childLeft n a i j + B.cell (n+1) j.val)) =
    Ico a (a + B.cell n i) := by
  have h := (finite_interval_split a
    (fun j : {j // p n j = i} => B.cell (n+1) j.val) (fun j => B.cell_zero (n+1) j.val)).choose_spec.2
  change (⋃ j : {j // p n j = i},
      Ico (B.childLeft n a i j) (B.childLeft n a i j + B.cell (n+1) j.val)) =
      Ico a (a + ∑ j : {j // p n j = i}, B.cell (n+1) j.val) at h
  have hsum : (∑ j : {j // p n j = i}, B.cell (n+1) j.val) = B.cell n i := by
    rw [B.cell_split n i]
    exact (Finset.sum_subtype (p := fun j => p n j = i) _ (fun _ => by simp) _).symm
  rwa [hsum] at h

noncomputable def lower : ∀ n, I n → ℝ
  | 0 => (finite_interval_split 0 (B.cell 0) (B.cell_zero 0)).choose
  | n+1 => fun i => B.childLeft n (lower n (p n i)) (p n i) ⟨i,rfl⟩

noncomputable def region (n : ℕ) (i : I n) : Set ℝ :=
  Ico (B.lower n i) (B.lower n i + B.cell n i)

lemma region_refine (n : ℕ) (i : I n) :
    (⋃ j : {j // p n j = i}, B.region (n+1) j.val) = B.region n i := by
  refine Eq.trans (iUnion_congr ?_) (B.child_partition n (B.lower n i) i)
  intro j
  rcases j with ⟨j,hj⟩
  subst i
  rfl

lemma region_nested (n : ℕ) (j : I (n+1)) :
    B.region (n+1) j ⊆ B.region n (p n j) := by
  intro x hx
  have h : x ∈ ⋃ k : {k // p n k = p n j}, B.region (n+1) k.val :=
    mem_iUnion.mpr ⟨⟨j,rfl⟩,hx⟩
  exact (B.region_refine n (p n j)) ▸ h

lemma region_cover (n : ℕ) : (⋃ i, B.region n i) = Ico 0 1 := by
  induction n with
  | zero =>
    have h := (finite_interval_split 0 (B.cell 0) (B.cell_zero 0)).choose_spec.2
    simpa only [region,lower,B.cell_total,zero_add] using h
  | succ n ih =>
    rw [← ih]
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨p n j,B.region_nested n j hj⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      have h : x ∈ ⋃ j : {j // p n j = i}, B.region (n+1) j.val :=
        (B.region_refine n i).symm ▸ hi
      obtain ⟨j,hj⟩ := mem_iUnion.mp h
      exact mem_iUnion.mpr ⟨j.val,hj⟩

lemma region_disjoint (n : ℕ) : Pairwise (Disjoint on B.region n) := by
  induction n with
  | zero =>
    exact (finite_interval_split 0 (B.cell 0) (B.cell_zero 0)).choose_spec.1
  | succ n ih =>
    intro i j hij
    by_cases hpij : p n i = p n j
    · let i' : {k // p n k = p n j} := ⟨i,hpij⟩
      let j' : {k // p n k = p n j} := ⟨j,rfl⟩
      have hh : i' ≠ j' := fun h => hij (congrArg Subtype.val h)
      have hq := (finite_interval_split (B.lower n (p n j))
        (fun a : {k // p n k = p n j} => B.cell (n+1) a.val)
        (fun a => B.cell_zero (n+1) a.val)).choose_spec.1 hh
      change Disjoint (B.region (n+1) i) (B.region (n+1) j)
      change Disjoint
        (Ico (B.childLeft n (B.lower n (p n j)) (p n j) i')
          (B.childLeft n (B.lower n (p n j)) (p n j) i' + B.cell (n+1) i))
        (B.region (n+1) j) at hq
      have he : ∀ a (h : p n i = a),
          B.lower (n+1) i = B.childLeft n (B.lower n a) a ⟨i,h⟩ := by
        intro a h
        subst a
        rfl
      change Disjoint (Ico (B.lower (n+1) i) (B.lower (n+1) i + B.cell (n+1) i))
        (B.region (n+1) j)
      rw [he (p n j) hpij]
      exact hq
    · exact (ih hpij).mono (B.region_nested n i) (B.region_nested n j)

lemma region_measurable (n : ℕ) (i : I n) : MeasurableSet (B.region n i) :=
  measurableSet_Ico

lemma region_mass (n : ℕ) (i : I n) : volume.real (B.region n i) = B.cell n i := by
  rw [region, Real.volume_real_Ico, add_sub_cancel_left,max_eq_left (B.cell_zero n i)]

end CoherentTables

#print axioms CoherentTables.region_refine
#print axioms CoherentTables.region_cover
#print axioms CoherentTables.region_mass
#print axioms CoherentTables.region_disjoint
end SparseHalfGraphon
