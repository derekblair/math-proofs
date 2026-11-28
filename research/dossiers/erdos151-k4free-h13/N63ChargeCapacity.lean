import N63TargetTen
import TwoChargedPivots

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12

variable {V : Type*} [DecidableEq V]
variable (L : V → V → Prop) [DecidableRel L]

theorem link_outside_excess_at_least_two_per_charger (S W : Finset V) (sub : W ⊆ S)
    (min2 : ∀ x ∈ S, 2 ≤ deg L S x) (min4 : ∀ x ∈ W, 4 ≤ deg L S x) :
    2*S.card + 2*W.card ≤ ∑ x ∈ S, deg L S x := by
  have no : Disjoint (S \ W) W := disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hx).2 hy)
  have ee : (S \ W)∪W = S := sdiff_union_of_subset sub
  have card := card_sdiff_add_card_eq_card sub
  have sum := sum_union (f:=fun x => deg L S x) no
  rw [ee] at sum
  have first : 2*(S\W).card ≤ ∑ x ∈ S\W, deg L S x := by
    have q := sum_le_sum (s:=S\W) (f:=fun _ => 2) (fun x hx => min2 x (mem_sdiff.mp hx).1)
    simpa [Nat.mul_comm] using q
  have second : 4*W.card ≤ ∑ x ∈ W, deg L S x := by
    have q := sum_le_sum (s:=W) (f:=fun _ => 4) (fun x hx => min4 x hx)
    simpa [Nat.mul_comm] using q
  omega

theorem bipartite_link_spokes_extend (S : Finset V) (bi : TwoChargedPivots.Bicuts L S)
    (color : V → V → Bool) :
    ∃ f : V → Bool, ∀ a ∈ S, ∀ b ∈ S, L a b →
      ¬ (f a = color a b ∧ f b = color a b) := by
  obtain ⟨P,Q,dis,eq,indP,indQ⟩ := bi
  let f (x : V) : Bool := decide (x∈P)
  refine ⟨f,?_⟩
  intro a ha b hb ab colors
  have isP (v : V) (hv : v∈P) : f v=true := by simp [f,hv]
  have isQ (v : V) (hv : v∈Q) : f v=false := by
    have hn : v∉P := fun p => disjoint_left.mp dis p hv
    simp [f,hn]
  rw [←eq] at ha hb
  rcases mem_union.mp ha with ap|aq <;> rcases mem_union.mp hb with bp|bq
  · exact indP a ap b bp ab
  · have e := colors.1.trans colors.2.symm
    rw [isP a ap,isQ b bq] at e
    contradiction
  · have e := colors.1.trans colors.2.symm
    rw [isQ a aq,isP b bp] at e
    contradiction
  · exact indQ a aq b bq ab

theorem actual_target_ten_at_most_one_of_density
    {U : Type*} [Fintype U] [DecidableEq U]
    (G C : U → U → Prop) [DecidableRel G] [DecidableRel C] (v : U) (W : Finset U)
    (sub : ∀ a b, C a b → G a b) (link : TriangleFreeLinks G)
    (symC : ∀ {a b}, C a b → C b a) (irrC : ∀ a, ¬C a a)
    (core10 : (neighbors C v).card = 10) (WV : W ⊆ neighbors C v)
    (min2 : ∀ a ∈ neighbors C v, 2 ≤ deg C (neighbors C v) a)
    (four : ∀ p ∈ W, (crossK C p v).card=4)
    (newPrice : ∀ p ∈ W, ∀ x ∈ crossK C p v,
        (neighbors G x∩neighbors G p).card = actualLinkDegree G C p x)
    (sharedPrice : ∀ p ∈ W, ∀ x ∈ crossK C p v, ∀ y ∈ crossK C p v, x≠y →
        ((neighbors G x∩neighbors G y)\insert p (neighbors G p)).card=0)
    (density : 27 ≤ ∑ a ∈ neighbors C v, deg C (neighbors C v) a)
    (noBi : ¬ TwoChargedPivots.Bicuts C (neighbors C v)) :
    W.card ≤ 1 := by
  by_contra h
  obtain ⟨p,hp,q,hq,pq⟩ := pick_two W (by omega)
  let S := neighbors C v
  have tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, C x a → C x b → ¬C a b := by
    intro x hx a ha b hb xa xb ab
    exact link v x a b (sub _ _ ((mem_neighbors C).mp hx)) (sub _ _ ((mem_neighbors C).mp ha))
      (sub _ _ ((mem_neighbors C).mp hb)) (sub _ _ xa) (sub _ _ ab) (sub _ _ xb)
  have h4 (a : U) (ha : a ∈ W) : deg C S a=4 := by
    unfold deg
    rw [target_near_eq C]
    exact four a ha
  have cross (a : U) (ha : a∈W) :=
    actual_link_cross_degree G C a v sub symC (newPrice a ha) (sharedPrice a ha)
  have nC : ¬C p q := by
    intro pp
    have qm : q ∈ near C S p := mem_filter.mpr ⟨WV hq,pp⟩
    have row := (target_link_row_degree C symC irrC S tf p (WV hp) (h4 p hp) min2 (cross p hp)).2.1 q qm
    have q4 := h4 q hq
    change S.card=10 at core10
    omega
  rcases TwoChargedPivots.ten_link_two_pivot_dichotomy C S core10 symC irrC tf
      (WV hp) (WV hq) pq nC (h4 p hp) (h4 q hq) (cross p hp) (cross q hq) with bi|low
  · exact noBi bi
  · change 27 ≤ ∑ a ∈ S, deg C S a at density
    omega

#print axioms link_outside_excess_at_least_two_per_charger
#print axioms bipartite_link_spokes_extend
#print axioms actual_target_ten_at_most_one_of_density
end Erdos151H13
