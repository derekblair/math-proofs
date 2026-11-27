import StabilityHalfTransfer
import PetersenUniform
import C5Uniform
open scoped BigOperators
namespace SparseHalfStability
variable {V I T J : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [Fintype I]
    [DecidableEq I] [Fintype T] [DecidableEq T] [LinearOrder T] [Fintype J]

def HasSparseFractional (G : V → V → Bool) : Prop :=
  ∃ r : V → ℝ, (∀ v, 0 ≤ r v ∧ r v ≤ 1/(Fintype.card V : ℝ)) ∧
    (∑ v, r v) = 1/2 ∧ edgeCost G r ≤ 1/50

theorem local_of_chart (B : T → T → Bool) (G : V → V → Bool) (p : V → I) (embed : I → T)
    (sv : ∀ u v, G u v = G v u) (st : ∀ a b, B a b = B b a) (lt : ∀ t, B t t = false)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (pat : ∀ s : Finset I, (∀ i ∈ s, ∀ j ∈ s, B (embed i) (embed j) = false) →
      ∃ a, ∀ i ∈ s, B a (embed i) = true)
    (codeg : ∀ a b, B a b = false → ∃ i, B a (embed i) = true ∧ B b (embed i) = true)
    (c eps τ wmin : ℝ) (hc : 0 ≤ c) (ea : 2*(1+c)*eps ≤ c^2)
    (hwn : c ≤ wmin) (ht : 0 < τ) (hs : (Fintype.card I + 1)*τ ≤ eps * Fintype.card V)
    (hn : 0 < Fintype.card V)
    (edits : ((directedErrors G (fun i j => B (embed i) (embed j)) p).card : ℝ) ≤ τ^2)
    (large : ∀ i, 2*τ < ((fiber p i).card : ℝ))
    (init : ∀ i, wmin*(Fintype.card V : ℝ) + τ ≤ ((fiber p i).card : ℝ))
    (hj : Nonempty J)
    (chart : ∀ w : T → ℝ, (∀ t, 0 ≤ w t) → (∑ t, w t) = 1 →
      (∀ i, wmin ≤ w (embed i)) →
      ∃ s : J → T → ℝ, (∀ j t, 0 ≤ s j t ∧ s j t ≤ w t) ∧
        (∀ j, ∑ t, s j t = 1/2) ∧
        (∀ a b, B a b = true → (Fintype.card J : ℝ)*c*w a*w b ≤ ∑ j, s j a*s j b) ∧
        (∑ j, edgeCost B (s j)) ≤ (Fintype.card J : ℝ)/50) :
    HasSparseFractional G := by
  have hpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hn
  obtain ⟨q,D,hD,_,fib,cov,deg⟩ := edit_template G B p embed sv st tf pat codeg τ ht edits large
  have fw (i : I) : wmin ≤ weight q (embed i) := by
    apply (le_div_iff₀ hpos).mpr
    linarith [fib i,init i]
  obtain ⟨s,ad,mass,cc,cost⟩ := chart (weight q) (fun t => by unfold weight; positivity)
    (weight_mass q hn) fw
  have hl (i : I) : c*(Fintype.card V : ℝ) ≤ (fiber q (embed i)).card := by
    apply (le_div_iff₀ hpos).mp
    exact hwn.trans (fw i)
  have hh : τ ≤ eps * (Fintype.card V : ℝ) := by
    have H := mul_nonneg (Nat.cast_nonneg (Fintype.card I) : (0:ℝ) ≤ _) ht.le
    linarith
  refine lift_and_transfer B G q sv st lt tf c eps hc ea ?_ ⟨D,cov,hD.trans hh⟩
    (fun v => (deg v).trans hs) s hj ad mass cc cost
  intro e he
  have A := (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).2.1
  have B' := (Finset.mem_sdiff.mp he).2
  have hE : pull B q e.1 e.2 = false := by
    by_contra hE
    exact B' (Finset.mem_filter.mpr ⟨Finset.mem_univ _,A,by simpa using hE⟩)
  exact repaired_common B q embed codeg hl e hE

#print axioms local_of_chart
end SparseHalfStability
