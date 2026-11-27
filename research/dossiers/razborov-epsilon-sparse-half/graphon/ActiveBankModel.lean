import ActiveFamilySideCaps
import SaturatedActivePairs
import OutsideGreedyModel
import BankDichotomy
import RestrictedAllocations

open Set MeasureTheory Function Filter
open scoped BigOperators
namespace SparseHalfGraphon

/-- A measure-correct active bank on the complement of the marked set.
It stores actual binary anchor rows; outside cross rectangles may be incomplete. -/
structure ActiveBank {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (K : Kernel Y)
    (A : Set Y) (I : Type*) where
  P : I→Set Y
  Q : I→Set Y
  R : I→Set Y
  meas : ∀ j, MeasurableSet (P j) ∧ MeasurableSet (Q j) ∧ MeasurableSet (R j)
  inside : ∀ j, P j∪Q j ⊆ Aᶜ
  inner : ∀ j, Disjoint (P j) (Q j)
  outer : Pairwise (Disjoint on fun j => P j∪Q j)
  edge : ∀ᵐ z ∂(μ.restrict Aᶜ).prod (μ.restrict Aᶜ), 0<K.W z → ∃ j,
    (z.1∈P j ∧ z.2∈Q j) ∨ (z.1∈Q j ∧ z.2∈P j)
  active : ∀ᵐ x ∂μ.restrict Aᶜ, x∈(⋃ j,P j∪Q j) ↔ 0<deg (μ.restrict Aᶜ) K x
  profiles : ∀ j, (P j=∅ ∧ Q j=∅) ∨
    (0<(μ.restrict Aᶜ).real (P j) ∧ 0<(μ.restrict Aᶜ).real (Q j) ∧
    (μ.restrict A).real (R j)=mass (μ.restrict A)/2 ∧
    (μ.restrict A).real (R j)ᶜ=mass (μ.restrict A)/2 ∧
    (∀ᵐ v ∂μ.restrict A, (fun x=>K.W (v,x)) =ᵐ[(μ.restrict Aᶜ).restrict (P j)] (fun _=>oneOn (R j) v)) ∧
    (∀ᵐ v ∂μ.restrict A, (fun x=>K.W (v,x)) =ᵐ[(μ.restrict Aᶜ).restrict (Q j)] (fun _=>oneOn (R j)ᶜ v)) ∧
    (∀ᵐ x ∂(μ.restrict Aᶜ).restrict (P j), (fun v=>K.W (x,v)) =ᵐ[μ.restrict A] oneOn (R j)) ∧
    (∀ᵐ x ∂(μ.restrict Aᶜ).restrict (Q j), (fun v=>K.W (x,v)) =ᵐ[μ.restrict A] oneOn (R j)ᶜ))
  cap : ∀ j, μ.real (P j)≤1/5 ∧ μ.real (Q j)≤1/5

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
variable {K : Kernel Y} {A : Set Y} {I : Type*} (B : ActiveBank μ K A I)

noncomputable def ActiveBank.p := larger10 μ B.P B.Q
noncomputable def ActiveBank.q := smaller10 μ B.P B.Q
noncomputable def ActiveBank.h := isolate10 μ Aᶜ B.P B.Q

lemma ActiveBank.p_upper : ∀ j, B.p j≤2 := by
  intro j
  unfold ActiveBank.p larger10
  have hx := B.cap j
  linarith [max_le hx.1 hx.2]

lemma ActiveBank.q_nonneg : ∀ j, 0≤B.q j := by
  intro j
  unfold ActiveBank.q smaller10
  positivity

lemma ActiveBank.q_le_p : ∀ j, B.q j≤B.p j := by
  intro j
  unfold ActiveBank.q ActiveBank.p smaller10 larger10
  have hx := (min_le_left (μ.real (B.P j)) (μ.real (B.Q j))).trans (le_max_left (μ.real (B.P j)) (μ.real (B.Q j)))
  linarith

lemma ActiveBank.h_nonneg : 0≤B.h := by
  unfold ActiveBank.h isolate10
  positivity

lemma ActiveBank.empty_of_p_zero (j : I) (h : B.p j=0) : B.P j=∅ ∧ B.Q j=∅ := by
  rcases B.profiles j with h0 | ⟨hp,hq,_⟩
  · exact h0
  · have hh := restrict_real_sub μ Aᶜ (B.P j) (B.meas j).1
      (fun _ x=>(B.inside j) (Or.inl x))
    rw [hh] at hp
    unfold ActiveBank.p larger10 at h
    linarith [le_max_left (μ.real (B.P j)) (μ.real (B.Q j))]

lemma ActiveBank.equal_caps (j : I) (c : ℝ) (hp : B.p j=c) (hq : B.q j=c) :
    μ.real (B.P j)=c/10 ∧ μ.real (B.Q j)=c/10 := by
  unfold ActiveBank.p larger10 at hp
  unfold ActiveBank.q smaller10 at hq
  constructor <;> linarith [min_le_left (μ.real (B.P j)) (μ.real (B.Q j)),
    min_le_right (μ.real (B.P j)) (μ.real (B.Q j)),
    le_max_left (μ.real (B.P j)) (μ.real (B.Q j)),
    le_max_right (μ.real (B.P j)) (μ.real (B.Q j))]

#print axioms ActiveBank.equal_caps
end SparseHalfGraphon
