import N63ChargeCapacity

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

/-- Every nonempty charging fiber has strict negative capacity, given
the geometric source prices and the high-order degree caps. -/
theorem actual_strict_receiver
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b) (symC : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬Lone G a b) (irrC : ∀ a, ¬C a a)
    (v : V) (W : Finset V) (Wne : W.Nonempty) (WV : W ⊆ neighbors C v)
    (core12 : (neighbors C v).card ≤ 12)
    (min2 : ∀ a ∈ neighbors C v, 2 ≤ deg C (neighbors C v) a)
    (min8 : ∀ a ∈ neighbors C v, 8 ≤ (neighbors C a).card)
    (max12 : ∀ a, (neighbors G a).card ≤ 12) (size63 : 63 ≤ Fintype.card V)
    (four : ∀ p ∈ W, (crossK C p v).card=4)
    (newPrice : ∀ p ∈ W, ∀ x ∈ crossK C p v,
        (neighbors G x∩neighbors G p).card = actualLinkDegree G C p x)
    (sharedPrice : ∀ p ∈ W, ∀ x ∈ crossK C p v, ∀ y ∈ crossK C p v, x≠y →
        ((neighbors G x∩neighbors G y)\insert p (neighbors G p)).card=0)
    (cap11 : (neighbors C v).card=11 → (∑ a ∈ neighbors C v, deg C (neighbors C v) a) ≤ 28)
    (cap12 : (neighbors C v).card=12 → (∑ a ∈ neighbors C v, deg C (neighbors C v) a) ≤ 24)
    (noBi : (neighbors C v).card=10 → ¬ TwoChargedPivots.Bicuts C (neighbors C v))
    (noFree : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V)) :
    (∑ a ∈ neighbors C v, deg C (neighbors C v) a) + W.card + 1 ≤ 3*(neighbors C v).card := by
  let S := neighbors C v
  let e := ∑ a ∈ S, deg C S a
  change e+W.card+1 ≤ 3*S.card
  change S.card ≤ 12 at core12
  obtain ⟨p,hp⟩ := Wne
  have pS := WV hp
  have tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, C x a → C x b → ¬C a b := by
    intro x hx a ha b hb xa xb ab
    exact link v x a b (sub _ _ ((mem_neighbors C).mp hx)) (sub _ _ ((mem_neighbors C).mp ha))
      (sub _ _ ((mem_neighbors C).mp hb)) (sub _ _ xa) (sub _ _ ab) (sub _ _ xb)
  have h4 (a : V) (ha : a ∈ W) : deg C S a=4 := by
    unfold deg
    rw [target_near_eq C]
    exact four a ha
  have cross := actual_link_cross_degree G C p v sub symC (newPrice p hp) (sharedPrice p hp)
  have c9 := (target_link_row_degree C symC irrC S tf p pS (h4 p hp) min2 cross).1
  have few (c10 : S.card ≤ 10) := actual_target_at_most_two G C v W sub link symC irrC c10
    WV min2 four newPrice sharedPrice
  have big := link_outside_excess_at_least_two_per_charger C S W WV min2 (fun a ha => (h4 a ha).ge)
  change 2*S.card+2*W.card ≤ e at big
  interval_cases h : S.card
  · have maxE : e≤24 := charged_target_order_nine_deficit C symC irrC S h tf p pS (h4 p hp) min2 cross
    have a := few (by omega)
    omega
  · have before : e < 30 := by
      by_contra! bad
      exact noFree (actual_charged_ten_strict G C sym irr link R41 sub symC coreNonlone irrC p v pS
        h (four p hp) min2 min8 max12 size63 (newPrice p hp) (sharedPrice p hp) bad)
    obtain ⟨m,hm⟩ := Erdos151Ramsey.even_degree_sum C S symC irrC
    change e=2*m at hm
    by_cases ed : 27 ≤ e
    · have a := actual_target_ten_at_most_one_of_density G C v W sub link symC irrC h WV min2
        four newPrice sharedPrice ed (noBi rfl)
      omega
    · have a := few (by omega)
      omega
  · have b : e≤28 := cap11 rfl
    omega
  · have b : e≤24 := cap12 rfl
    omega

#print axioms actual_strict_receiver
end Erdos151H13
