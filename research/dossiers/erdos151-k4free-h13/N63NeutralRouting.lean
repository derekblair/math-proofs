import N63SenderCensus
import N63StrictReceiver
import H13Charge

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

private def lsize (v : V) : ℕ := (neighbors C v).card
private def degreeSum (v : V) : ℕ := ∑ a ∈ neighbors C v, deg C (neighbors C v) a
private def score (v : V) : ℤ := (degreeSum C v : ℤ) - 3*(lsize C v : ℤ)

/-- The checked dense-nine census and strict actual receiver estimates
force equality in every link score. No external local enumeration input. -/
theorem actual_neutral_by_routing
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b) (symC : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬Lone G a b) (irrC : ∀ a, ¬C a a)
    (coreMin : ∀ v, 0 < lsize C v → 8 ≤ lsize C v)
    (min2 : ∀ v, ∀ a ∈ neighbors C v, 2 ≤ deg C (neighbors C v) a)
    (max12 : ∀ a, (neighbors G a).card ≤ 12) (size63 : 63 ≤ Fintype.card V)
    (cap8 : ∀ v, lsize C v=8 → degreeSum C v ≤ 24)
    (cap10 : ∀ v, lsize C v=10 → degreeSum C v ≤ 30)
    (cap11 : ∀ v, lsize C v=11 → degreeSum C v ≤ 28)
    (cap12 : ∀ v, lsize C v=12 → degreeSum C v ≤ 24)
    (noBi : ∀ v, lsize C v=10 → ¬ TwoChargedPivots.Bicuts C (neighbors C v))
    (noFree : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V))
    (global : 0 ≤ ∑ v : V, score C v) :
    ∀ v, degreeSum C v = 3*lsize C v := by
  classical
  have min8 (v : V) (a : V) (ha : a∈neighbors C v) : 8 ≤ (neighbors C a).card := by
    apply coreMin a
    exact Finset.card_pos.mpr ⟨v,(mem_neighbors C).mpr (symC ((mem_neighbors C).mp ha))⟩
  have maxi (v : V) : lsize C v≤12 := by
    exact (Finset.card_le_card (s:=neighbors C v) (t:=neighbors G v)
      (fun x hx => (mem_neighbors G).mpr (sub _ _ ((mem_neighbors C).mp hx)))).trans (max12 v)
  have positive_sender (v : V) (hp : 0 < score C v) : ∃ w, SenderData G C v w := by
    have hPos : 0<lsize C v := by
      by_contra! h
      have S0 : neighbors C v = ∅ := card_eq_zero.mp (by change lsize C v=0; omega)
      simp [score,lsize,degreeSum,S0] at hp
    have hmin := coreMin v hPos
    have hmax := maxi v
    have hq : 3*(lsize C v)<degreeSum C v := by
      unfold score at hp
      omega
    have r9 : lsize C v=9 := by
      by_contra h
      have nn : lsize C v=8 ∨ lsize C v=10 ∨ lsize C v=11 ∨ lsize C v=12 := by omega
      rcases nn with r|r|r|r
      · have := cap8 v r; omega
      · have := cap10 v r; omega
      · have := cap11 v r; omega
      · have := cap12 v r; omega
    exact sender_of_dense_nine G C sym irr link R41 sub symC coreNonlone v r9 (min2 v)
      (by change 28 ≤ degreeSum C v; omega) (min8 v) max12 size63 noFree
  let route (v : V) : V := if h : 0 < score C v then Classical.choose (positive_sender v h) else v
  have data (v : V) (hv : 0 < score C v) : SenderData G C v (route v) := by
    unfold route
    rw [dif_pos hv]
    exact Classical.choose_spec (positive_sender v hv)
  let W (v : V) := (H13Charge.positive Finset.univ (score C)).filter (fun w => route w=v)
  have sdata (v : V) (p : V) (hp : p∈W v) : SenderData G C p v := by
    obtain ⟨h,q⟩ := mem_filter.mp hp
    have d := data p (mem_filter.mp h).2
    rwa [q] at d
  have receiver (v : V) (hv : (W v).Nonempty) : degreeSum C v + (W v).card + 1 ≤ 3*lsize C v := by
    have Wv : W v ⊆ neighbors C v := fun p hp => (mem_neighbors C).mpr (symC (sdata v p hp).edge)
    exact actual_strict_receiver G C sym irr link R41 sub symC coreNonlone irrC v (W v) hv Wv
      (maxi v) (min2 v) (min8 v) max12 size63
      (fun p hp => (sdata v p hp).four) (fun p hp => (sdata v p hp).price)
      (fun p hp => (sdata v p hp).shared) (cap11 v) (cap12 v) (noBi v) noFree
  have wp (p : V) (h : 0 < score C p) : p∈W (route p) :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  have tt := H13Charge.unit_routing_forces_neutral Finset.univ (score C) route
    (fun w _ hw => by
      have q := data w hw
      have h3 : lsize C w=9 := q.coreNine
      have h4 : degreeSum C w=28 := q.score28
      simp [score,h3,h4])
    (fun w _ hw => by
      refine ⟨mem_univ _,?_⟩
      have R := receiver (route w) ⟨w,wp w hw⟩
      unfold score
      omega)
    (fun v _ h => by
      obtain ⟨w,_,hw,ww⟩ := h
      have hv : w∈W v := ww ▸ wp w hw
      have R := receiver v ⟨w,hv⟩
      change ((W v).card : ℤ) < -score C v
      unfold score
      omega) global
  intro v
  have q := tt v (mem_univ _)
  unfold score at q
  omega

#print axioms actual_neutral_by_routing
end Erdos151H13
