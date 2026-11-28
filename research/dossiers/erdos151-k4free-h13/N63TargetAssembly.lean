import N63CrossCharge
import HubChargeCapacity

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem target_near_eq (p v : V) : near C (neighbors C v) p = crossK C p v := by
  ext x
  simp [near,crossK,mem_neighbors,and_comm]

theorem actual_link_cross_degree (p v : V)
    (sub : ∀ a b, C a b → G a b) (symC : ∀ {a b}, C a b → C b a)
    (newPrice : ∀ x ∈ crossK C p v,
        (neighbors G x∩neighbors G p).card = actualLinkDegree G C p x)
    (sharedPrice : ∀ x ∈ crossK C p v, ∀ y ∈ crossK C p v, x≠y →
        ((neighbors G x∩neighbors G y)\insert p (neighbors G p)).card=0) :
    ∀ z ∈ neighbors C v, z ≠ p → ¬C p z → deg C (near C (neighbors C v) p) z ≤ 1 := by
  intro z zv nzp nC
  have nzK : z ∉ crossK C p v := fun h => nC ((mem_neighbors C).mp (mem_inter.mp h).1)
  have h := actual_target_core_cross_at_most_one G C p v z sub newPrice sharedPrice zv nzp nzK
  rw [target_near_eq C p v]
  unfold deg near
  have eq : ((crossK C p v).filter (C z)) = ((crossK C p v).filter fun x => C x z) := by
    ext x
    simp only [mem_filter]
    exact and_congr_right (fun _ => ⟨symC,symC⟩)
  rwa [eq]

/-- At small negative targets, no more than two unit surplus vertices can
route to the same actual vertex. This only uses core degree at least two
on the link, and the already checked attachment/overlap prices. -/
theorem actual_target_at_most_two (v : V) (W : Finset V)
    (sub : ∀ a b, C a b → G a b) (link : TriangleFreeLinks G)
    (symC : ∀ {a b}, C a b → C b a) (irrC : ∀ a, ¬C a a)
    (core10 : (neighbors C v).card ≤ 10) (WV : W ⊆ neighbors C v)
    (min2 : ∀ a ∈ neighbors C v, 2 ≤ deg C (neighbors C v) a)
    (four : ∀ p ∈ W, (crossK C p v).card=4)
    (newPrice : ∀ p ∈ W, ∀ x ∈ crossK C p v,
        (neighbors G x∩neighbors G p).card = actualLinkDegree G C p x)
    (sharedPrice : ∀ p ∈ W, ∀ x ∈ crossK C p v, ∀ y ∈ crossK C p v, x≠y →
        ((neighbors G x∩neighbors G y)\insert p (neighbors G p)).card=0) :
    W.card ≤ 2 := by
  let S := neighbors C v
  have tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, C x a → C x b → ¬C a b := by
    intro x hx a ha b hb xa xb ab
    exact link v x a b (sub _ _ ((mem_neighbors C).mp hx)) (sub _ _ ((mem_neighbors C).mp ha))
      (sub _ _ ((mem_neighbors C).mp hb)) (sub _ _ xa) (sub _ _ ab) (sub _ _ xb)
  have h4 (p : V) (hp : p ∈ W) : deg C S p=4 := by
    unfold deg
    rw [target_near_eq C]
    exact four p hp
  have cross (p : V) (hp : p∈W) :=
    actual_link_cross_degree G C p v sub symC (newPrice p hp) (sharedPrice p hp)
  have separate (p : V) (hp : p ∈ W) (x : V) (hx : x ∈ crossK C p v) : x ∉ W := by
    intro hW
    have w := (target_link_row_degree C symC irrC S tf p (WV hp) (h4 p hp) min2 (cross p hp)).2.1
    have xx : x ∈ near C S p := by rwa [target_near_eq C]
    have b := w x xx
    have a := h4 x hW
    change S.card ≤ 10 at core10
    omega
  apply at_most_two_charged S W (fun p => crossK C p v) (by change (neighbors C v).card ≤ 11; omega) WV
  · intro p hp x hx
    exact mem_sdiff.mpr ⟨(mem_inter.mp hx).2,separate p hp x hx⟩
  · intro p hp
    exact (four p hp).ge
  · intro p hp q hq pq
    have noPQ : ¬C p q := fun h => separate p hp q
      (mem_inter.mpr ⟨(mem_neighbors C).mpr h,WV hq⟩) hq
    have b := cross p hp q (WV hq) pq.symm noPQ
    rw [target_near_eq C] at b
    apply (card_le_card (t:=near C (crossK C p v) q) ?_).trans b
    intro x hx
    obtain ⟨lp,lq⟩ := mem_inter.mp hx
    exact mem_filter.mpr ⟨lp,(mem_neighbors C).mp (mem_inter.mp lq).1⟩

#print axioms actual_link_cross_degree
#print axioms actual_target_at_most_two
end Erdos151H13
