import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators
namespace DirectedBoxDSP

variable {I K : Type*} [Fintype I] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def progress (i : I) (p : I→K) : K :=
  ∑ j, (p i-p j)

def ownIncrease (i : I) (p q : I→K) (j : I) : K :=
  (q i-q j)-(p i-p j)

theorem progress_diff (i : I) (p q : I→K) :
    progress i q-progress i p = ∑ j, ownIncrease i p q j := by
  unfold progress ownIncrease
  simp [sub_eq_add_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib]

theorem progress_monotone (i : I) (p q : I→K)
    (mono : ∀ j, p i-p j ≤ q i-q j) : progress i p ≤ progress i q :=
  Finset.sum_le_sum (fun j _ => mono j)

/-- A basis pair coordinate is 1-Lipschitz as a function of progress
on each shortest path, for an arbitrary pair of potentials. -/
theorem pair_lipschitz (i a b : I) (p q : I→K)
    (mono : ∀ j, p i-p j ≤ q i-q j) :
    |(q a-q b)-(p a-p b)| ≤ progress i q-progress i p := by
  have pos : ∀ j, 0 ≤ ownIncrease i p q j := fun j => sub_nonneg.mpr (mono j)
  have one (j : I) : ownIncrease i p q j ≤ ∑ l, ownIncrease i p q l :=
    Finset.single_le_sum (fun z _ => pos z) (Finset.mem_univ _)
  have delta : (q a-q b)-(p a-p b) =
      ownIncrease i p q b - ownIncrease i p q a := by unfold ownIncrease; linarith
  rw [delta,progress_diff]
  exact abs_le.mpr ⟨by linarith [one a,pos b], by linarith [one b,pos a]⟩

/-- In a box of maximum coordinate width W, all progress values
of a fixed commodity inside the box lie in an interval of width
at most twice W per own coordinate. -/
theorem box_progress_spread (i b : I) (p q : I→K) (W : K)
    (box : ∀ a, |(q a-q b)-(p a-p b)| ≤ W) :
    progress i q-progress i p ≤ (Fintype.card I:K)*(2*W) := by
  rw [progress_diff]
  calc
    _ ≤ ∑ _j : I, 2*W := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨_,h1⟩ := abs_le.mp (box i)
      obtain ⟨h2,_⟩ := abs_le.mp (box j)
      unfold ownIncrease
      linarith
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- If an arc is tight at any commodity and all pair-coordinate
positions are identical, every potential rises by the positive arc
weight. Thus internal zero-position arcs share one acyclic order. -/
theorem tied_arc_common_progress (i b a : I) (p q : I→K) (w : K)
    (tight : q i-p i=w) (ties : ∀ j, q j-q b=p j-p b) :
    q a-p a=w := by
  have ha := ties a
  have hi := ties i
  linarith

/-- One cut coordinate is a difference of only two own coordinates,
so clipping pays their total increments, not the sum over k coordinates. -/
theorem pair_lipschitz_two_charges (i a b : I) (p q : I→K)
    (mono : ∀ j, p i-p j ≤ q i-q j) :
    |(q a-q b)-(p a-p b)| ≤ ownIncrease i p q a + ownIncrease i p q b := by
  have va := mono a
  have vb := mono b
  unfold ownIncrease
  apply abs_le.mpr
  constructor <;> linarith

private def width (q : K×K) : K := q.2-q.1

/-- Monotone clipped portions may have gaps between them, but their
positive increments telescope inside the enclosing width. -/
theorem packed_width (xs : List (K×K)) (lo hi : K)
    (hr : lo≤hi)
    (ord : xs.Pairwise (fun a b => a.2≤b.1))
    (left : ∀ a ∈ xs, lo≤a.1) (right : ∀ a ∈ xs, a.2≤hi) :
    (xs.map width).sum ≤ hi-lo := by
  induction xs generalizing lo with
  | nil => simp; linarith
  | cons a tl ih =>
    have pp := List.pairwise_cons.mp ord
    have hiA := right a (by simp)
    have loA := left a (by simp)
    have ht := ih a.2 hiA pp.2 pp.1 (fun b hb => right b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons,width]
    change (a.2-a.1)+(tl.map width).sum ≤ hi-lo
    linarith

#print axioms pair_lipschitz_two_charges
#print axioms packed_width
#print axioms pair_lipschitz
#print axioms box_progress_spread
#print axioms tied_arc_common_progress
end DirectedBoxDSP
