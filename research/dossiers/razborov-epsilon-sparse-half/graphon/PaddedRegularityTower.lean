import RegularityTower

open MeasureTheory Set Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

def towerCapacity (k : ℕ) (fuel : ℕ → ℕ) : ℕ → ℕ
  | 0 => k
  | n+1 => towerCapacity k fuel n * 4^(fuel n)

lemma towerCapacity_pos {k : ℕ} (hk : 0 < k) (fuel : ℕ → ℕ) :
    ∀ n, 0 < towerCapacity k fuel n := by
  intro n
  induction n with
  | zero => exact hk
  | succ n ih => exact Nat.mul_pos ih (pow_pos (by decide) _)

lemma meanBlock_embed {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {I J : Type*} (e : I ↪ J) (c : Y → I) (f : Y → ℝ) :
    meanBlock ν (e ∘ c) f = meanBlock ν c f := by
  funext x
  have he : cell (e ∘ c) (e (c x))=cell c (c x) := by
    ext y
    exact e.injective.eq_iff
  unfold meanBlock meanCell
  change (∫ y in cell (e ∘ c) (e (c x)), f y ∂ν)/ν.real (cell (e ∘ c) (e (c x)))=_
  rw [he]

lemma blockKernel_W_embed {I J : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSpace J] [MeasurableSingletonClass I]
    [MeasurableSingletonClass J] (e : I ↪ J) (c : X → I) (K : Kernel X)
    (hc : Measurable c) (hec : Measurable (e ∘ c)) :
    (blockKernel μ K (e ∘ c) hec).W = (blockKernel μ K c hc).W := by
  let E : I × I ↪ J × J :=
    ⟨Prod.map e e, fun _ _ h => Prod.ext (e.injective (congrArg Prod.fst h))
      (e.injective (congrArg Prod.snd h))⟩
  change meanBlock (μ.prod μ) (pairLabel (e ∘ c)) K.W = _
  have he : pairLabel (e ∘ c) = E ∘ pairLabel c := rfl
  rw [he]
  exact meanBlock_embed (μ.prod μ) E (pairLabel c) K.W

structure PaddedTower (d : ℕ → ℕ) where
  label : ∀ n, X → Fin (d n)
  measurable_label : ∀ n, Measurable (label n)
  parent : ∀ n, Fin (d (n+1)) → Fin (d n)
  parent_exact : ∀ n x, label n x = parent n (label (n+1) x)

def finPad {a b : ℕ} (h : a ≤ b) : Fin a ↪ Fin b :=
  ⟨Fin.castLE h, fun _ _ h => Fin.ext (congrArg (fun z : Fin b => z.val) h)⟩

/-- For a slot outside the actual fine partition, the parent is a fixed
fallback. Such a slot is not visited by any point. -/
def paddedParent {a b A B : ℕ} (ha : a ≤ A) (_hb : b ≤ B)
    (init : Fin A) (p : Fin b → Fin a) (j : Fin B) : Fin A :=
  if h : j.val < b then finPad ha (p ⟨j.val,h⟩) else init

lemma paddedParent_real {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (init : Fin A) (p : Fin b → Fin a) (j : Fin b) :
    paddedParent ha hb init p (finPad hb j) = finPad ha (p j) := by
  change (if h : j.val < b then finPad ha (p ⟨j.val,h⟩) else init) = _
  rw [dite_eq_left j.isLt]

theorem uniformly_padded_marked_tower {k : ℕ} (hk : 0 < k)
    (m : X → Fin k) (hm : Measurable m)
    (K : Kernel X) (hμ : mass μ = 1)
    (eps : ℕ → ℝ) (fuel : ℕ → ℕ) (he : ∀ n, 0 < eps n)
    (hf : ∀ n, 1 < ((fuel n : ℝ)+1)*(eps n)^2) :
    ∃ A : PaddedTower (X := X) (towerCapacity k fuel),
      A.label 0 = m ∧
      ∀ n, CutBound μ K (blockKernel μ K (A.label (n+1)) (A.measurable_label (n+1))) (eps n) := by
  classical
  let P : ColorPartition X := ⟨k,m,hm⟩
  obtain ⟨Q,hQ,hq⟩ := regularity_tower μ K hμ eps fuel he hf P
  have hc : ∀ n, (Q n).size ≤ towerCapacity k fuel n := by
    intro n
    induction n with
    | zero => rw [hQ]; exact le_rfl
    | succ n ih => exact (hq n).2.1.trans (Nat.mul_le_mul_right _ ih)
  let e (n : ℕ) := finPad (hc n)
  let L (n : ℕ) := e n ∘ (Q n).label
  have mL (n : ℕ) : Measurable (L n) :=
    (measurable_of_countable (e n)).comp (Q n).measurable_label
  let p (n : ℕ) := Classical.choose (hq n).1
  have pp (n : ℕ) (x : X) : (Q n).label x = p n ((Q (n+1)).label x) :=
    Classical.choose_spec (hq n).1 x
  let padp (n : ℕ) := paddedParent (hc n) (hc (n+1))
    ⟨0,towerCapacity_pos hk fuel n⟩ (p n)
  have par (n : ℕ) (x : X) : L n x = padp n (L (n+1) x) := by
    change e n ((Q n).label x) =
      paddedParent (hc n) (hc (n+1)) _ (p n) (finPad (hc (n+1)) ((Q (n+1)).label x))
    rw [paddedParent_real,pp n x]
  refine ⟨⟨L,mL,padp,par⟩, ?_, ?_⟩
  · funext x
    change e 0 ((Q 0).label x) = m x
    apply Fin.ext
    change ((Q 0).label x).val = (m x).val
    rw [hQ]
  · intro n
    have H := blockKernel_W_embed μ (e (n+1)) ((Q (n+1)).label) K
      ((Q (n+1)).measurable_label) (mL (n+1))
    have eq : blockKernel μ K (L (n+1)) (mL (n+1)) = partitionKernel μ K (Q (n+1)) := by
      cases h₁ : blockKernel μ K (L (n+1)) (mL (n+1))
      cases h₂ : partitionKernel μ K (Q (n+1))
      change (blockKernel μ K (L (n+1)) (mL (n+1))).W =
        (partitionKernel μ K (Q (n+1))).W at H
      rw [h₁,h₂] at H
      congr
    change CutBound μ K (blockKernel μ K (L (n+1)) (mL (n+1))) (eps n)
    rw [eq]
    exact (hq n).2.2

#print axioms uniformly_padded_marked_tower
end SparseHalfGraphon
