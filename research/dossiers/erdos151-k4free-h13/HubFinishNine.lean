import HubThin
import NineLinkPivot

namespace Erdos151H13
open Erdős151 Erdos151H12
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

/-- Actual core-degree-nine hub with at least 14 core link edges:
the ambient induced nine-link gives a safe nonadjacent pivot pair,
and Lean constructs a free set of 13. -/
theorem dense_core_nine_free13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (Csym : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (w : V) (r : (neighbors C w).card = 9)
    (coreMin : ∀ x, C w x → 8 ≤ (neighbors C x).card)
    (max : ∀ x, (neighbors G x).card ≤ 12) (n : 64 ≤ Fintype.card V)
    (dense : 28 ≤ ∑ a ∈ neighbors C w, NineLinkPivot.deg C (neighbors C w) a) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  let S := neighbors C w
  have sx (x : V) (h : x ∈ S) : G w x := sub w x ((mem_neighbors C).mp h)
  have localTF : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, G x a → G x b → ¬ G a b := by
    intro x hx a ha b hb xa xb h
    exact link w x a b (sx x hx) (sx a ha) (sx b hb) xa h xb
  have dom : ∀ a ∈ S, NineLinkPivot.deg C S a ≤ NineLinkPivot.deg G S a := by
    intro a ha
    apply Finset.card_le_card
    intro b hb
    obtain ⟨hs, hc⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hs,sub a b hc⟩
  have denseG := dense.trans (Finset.sum_le_sum dom)
  obtain ⟨x,hx,y,hy,xyne,hxy,dx,dy⟩ :=
    NineLinkPivot.ambient_nine_link_pivot G sym irr S localTF r denseG
  have oldx := (mem_neighbors C).mp hx
  have oldy := (mem_neighbors C).mp hy
  have lcard (v : V) :
      NineLinkPivot.deg G S v ≤ (neighbors G v ∩ neighbors G w).card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨sa,va⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr va,(mem_neighbors G).mpr (sx a sa)⟩
  have both :
      NineLinkPivot.deg G (NineLinkPivot.near G S x) y ≤
        ((neighbors G x∩neighbors G w)∩(neighbors G y∩neighbors G w)).card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨sa,ya⟩ := Finset.mem_filter.mp ha
    obtain ⟨sa,xa⟩ := Finset.mem_filter.mp sa
    have wa := (mem_neighbors G).mpr (sx a sa)
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr xa,wa⟩,
      Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr ya,wa⟩⟩
  have b3 : 3 ≤ (neighbors G y∩neighbors G w).card := by
    rcases dy with h|h
    · exact (by omega : 3 ≤ NineLinkPivot.deg G S y).trans (lcard y)
    · exact h.1.trans (lcard y)
  have alt : 4 ≤ (neighbors G y∩neighbors G w).card ∨
    2 ≤ ((neighbors G x∩neighbors G w)∩(neighbors G y∩neighbors G w)).card :=
    dy.elim (fun h => Or.inl (h.trans (lcard y))) (fun h => Or.inr (h.2.trans both))
  exact three_hub_free13 G C sym irr link R41 sub coreNonlone x w y
    (Csym oldx) (Csym oldy) hxy xyne (coreMin x oldx) (coreMin y oldy)
    r.ge n (by have hx := max x; have hy := max y; have hw := max w; omega)
    (dx.trans (lcard x)) b3 alt

#print axioms dense_core_nine_free13
end Erdos151H13
