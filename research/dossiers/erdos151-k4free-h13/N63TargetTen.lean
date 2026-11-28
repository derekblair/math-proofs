import N63TargetDeficit
import N63TargetAssembly
import N63TwoHighPrice

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12 Erdos151Ramsey

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

/-- A neutral ten-vertex link cannot receive a charge. Extracting its
two pivots uses only actual graph adjacency and the five-vertex equality,
not a separate marked-chart catalogue. -/
theorem actual_charged_ten_strict
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b) (symC : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬Lone G a b) (irrC : ∀ a, ¬C a a)
    (p v : V) (pv : p ∈ neighbors C v)
    (size10 : (neighbors C v).card=10) (four : (crossK C p v).card=4)
    (min2 : ∀ a ∈ neighbors C v, 2 ≤ deg C (neighbors C v) a)
    (min8 : ∀ a ∈ neighbors C v, 8 ≤ (neighbors C a).card)
    (max12 : ∀ a, (neighbors G a).card ≤ 12) (size63 : 63 ≤ Fintype.card V)
    (newPrice : ∀ x ∈ crossK C p v,
        (neighbors G x∩neighbors G p).card = actualLinkDegree G C p x)
    (sharedPrice : ∀ x ∈ crossK C p v, ∀ y ∈ crossK C p v, x≠y →
        ((neighbors G x∩neighbors G y)\insert p (neighbors G p)).card=0)
    (density : 30 ≤ ∑ a ∈ neighbors C v, deg C (neighbors C v) a) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  let S := neighbors C v
  let K := near C S p
  let E := S \ insert p K
  have crossK' : K = crossK C p v := target_near_eq C p v
  have k4 : K.card=4 := crossK'.symm ▸ four
  have bound := actual_link_cross_degree G C p v sub symC newPrice sharedPrice
  have fromCore (z : V) (hz : z ∈ S) : G v z := sub _ _ ((mem_neighbors C).mp hz)
  have tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, C x a → C x b → ¬C a b := by
    intro x hx a ha b hb xa xb ab
    exact link v x a b (fromCore x hx) (fromCore a ha) (fromCore b hb) (sub _ _ xa) (sub _ _ ab) (sub _ _ xb)
  obtain ⟨crossExactly,x,hx,y,hy,yx,nxy,dx,dy⟩ :=
    charged_target_ten_equality C symC irrC S size10 tf p pv k4 min2 bound density
  have es (z : V) (hz : z∈E) : z∈S := (mem_sdiff.mp hz).1
  have ks : K ⊆ S := filter_subset _ _
  have crossCap (z : V) (hz : z∈E) : (K.filter fun a => G a z).card ≤ 1 := by
    rw [crossK']
    obtain ⟨zs,hn⟩ := mem_sdiff.mp hz
    refine actual_target_cross_at_most_one G C p v z sub newPrice sharedPrice zs ?_ ?_
    · exact fun h => hn (mem_insert.mpr (Or.inl h))
    · exact fun h => hn (mem_insert.mpr (Or.inr (crossK'.symm ▸ h)))
  have nGxy : ¬ G x y := by
    obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (near C E x).card by rw [show (near C E x).card=3 from dx]; decide)
    have hz' : z∈near C E y := by rwa [dy]
    have zs := es z (mem_filter.mp hz).1
    intro h
    exact link v z x y (fromCore z zs) (fromCore x (es x hx)) (fromCore y (es y hy))
      (sym (sub _ _ (mem_filter.mp hz).2)) h (sym (sub _ _ (mem_filter.mp hz').2))
  have deg4 (z : V) (hz : z ∈ E) (hz3 : (near C E z).card=3) :
      4 ≤ actualLinkDegree G C v z := by
    let U := near C E z
    let D := near C K z
    have d1 : D.card=1 := crossExactly z hz
    have both : U∪D ⊆ neighbors G z∩neighbors C v := by
      intro a ha
      rcases mem_union.mp ha with ha|ha
      · obtain ⟨he,ce⟩ := mem_filter.mp ha
        exact mem_inter.mpr ⟨(mem_neighbors G).mpr (sub _ _ ce),es a he⟩
      · obtain ⟨hk,ce⟩ := mem_filter.mp ha
        exact mem_inter.mpr ⟨(mem_neighbors G).mpr (sub _ _ ce),ks hk⟩
    have dis : Disjoint U D := disjoint_left.mpr (fun a hu hd =>
      (mem_sdiff.mp (mem_filter.mp hu).1).2 (mem_insert.mpr (Or.inr (mem_filter.mp hd).1)))
    have c := card_le_card both
    rw [card_union_of_disjoint dis,d1] at c
    change U.card=3 at hz3
    unfold actualLinkDegree
    omega
  let X := K.filter fun a => G a x
  let Y := K.filter fun a => G a y
  let A := K \ (X∪Y)
  have hc : (X∪Y).card ≤ 2 := by
    have := card_union_le X Y
    have a := crossCap x hx
    have b := crossCap y hy
    change X.card ≤ 1 at a
    change Y.card ≤ 1 at b
    omega
  have ac : 2 ≤ A.card := by
    have he := card_sdiff_add_card_eq_card (union_subset (filter_subset _ _) (filter_subset _ _) :
      X∪Y ⊆ K)
    change A.card+(X∪Y).card=K.card at he
    omega
  have keep : ∀ z ∈ A, C v z ∧ z≠x ∧ z≠y ∧ ¬G x z ∧ ¬G y z := by
    intro z hz
    obtain ⟨zk,hn⟩ := mem_sdiff.mp hz
    have ne (u : V) (hu : u ∈ E) : z ≠ u := by
      intro eq
      exact (mem_sdiff.mp hu).2 (mem_insert.mpr (Or.inr (eq ▸ zk)))
    exact ⟨(mem_neighbors C).mp (ks zk),ne x hx,ne y hy,
      fun h => hn (mem_union_left _ (mem_filter.mpr ⟨zk,sym h⟩)),
      fun h => hn (mem_union_right _ (mem_filter.mpr ⟨zk,sym h⟩))⟩
  have freeA : Independent G A := by
    intro z hz t ht h
    have zk := (mem_sdiff.mp hz).1
    have tk := (mem_sdiff.mp ht).1
    exact link v p z t (fromCore p pv) (fromCore z (ks zk)) (fromCore t (ks tk))
      (sub _ _ (mem_filter.mp zk).2) h (sub _ _ (mem_filter.mp tk).2)
  exact free13_of_two_high_center_two G C sym irr link R41 sub symC coreNonlone x v y
    ((mem_neighbors C).mp (es x hx)) ((mem_neighbors C).mp (es y hy)) nGxy yx.symm
    (min8 x (es x hx)) (min8 y (es y hy)) (deg4 x hx dx) (deg4 y hy (by rwa [dy]))
    A keep freeA ac size63 (by have := max12 x; have := max12 y; have := max12 v; omega)

#print axioms actual_charged_ten_strict
end Erdos151H13
