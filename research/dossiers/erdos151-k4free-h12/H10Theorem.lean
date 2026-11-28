import H10Descent
import CoreExtract
import Mathlib.Data.Fintype.Card

namespace Erdős151.H10
open Upper

variable {V : Type*} [Fintype V]

theorem ramsey_has_free_ten (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G) (hn : 36 ≤ Fintype.card V)
    (r : BikovLocal.Ramsey G) :
    ∃ T : Finset V, 10 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  by_contra! bad
  have cap : FreeCap G 9 := by
    intro T hT
    by_contra h
    exact bad T (by omega) hT
  obtain ⟨C,sub,symC,_,_,_,⟨a,b,hab⟩,minC,two⟩ :=
    BikovLocal.extract_core G (fun {_ _} h => sym h) irr (fun w x y z wx wy wz xy xz yz =>
      link w x y z wx wy wz xy yz xz) r
  have cm (u : V) (hu : (nbr C u).Nonempty) : 8 ≤ (nbr C u).card := by
    obtain ⟨v,hv⟩ := hu
    have h := minC u ⟨v,(Finset.mem_filter.mp hv).2⟩
    simpa only [Fintype.card_subtype, nbr] using h
  have book (u v : V) (hv : v ∈ nbr C u) : 2 ≤ ((nbr C u).filter (C v)).card := by
    obtain ⟨x,y,hxy,hx,hy⟩ := two u v (Finset.mem_filter.mp hv).2
    have hsub : ({x,y} : Finset V) ⊆ (nbr C u).filter (C v) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl|rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx.1⟩,hx.2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy.1⟩,hy.2⟩
    have hcard : ({x,y} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem,Finset.card_singleton]
      simpa using hxy
    simpa [hcard] using Finset.card_le_card hsub
  exact h10_exclude_core (G := G) (C := C) sym (fun {_ _} h => symC h) irr link cap (fun {_ _} h => sub h) hn cm book a
    ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab⟩⟩

/-- Ramsey lower bound hypothesis in the exact form H(n)≥10. -/
def TriangleIndependentTen (V : Type*) [Fintype V] : Prop :=
  ∀ H : V → V → Prop, (∀ {a b}, H a b → H b a) →
    (∀ a, ¬ H a a) → Erdos151Ramsey.TriangleFree H →
    ∃ S : Finset V, 10 ≤ S.card ∧ Erdos151Ramsey.Independent H S

theorem k4free_of_triangle_independent_ten (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G) (hn : 36 ≤ Fintype.card V)
    (H : TriangleIndependentTen V) :
    ∃ T : Finset V, 10 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  by_cases r : BikovLocal.Ramsey G
  · exact ramsey_has_free_ten G sym irr link hn r
  · unfold BikovLocal.Ramsey at r
    push Not at r
    obtain ⟨c,cs,safe⟩ := r
    have va a b d (ab : G a b) (bd : G b d) (ad : G a d) :
        ¬ (c a b = c b d ∧ c a b = c a d) := by
      intro h
      exact safe a b d ab bd (sym ad) ⟨h.1,h.1.symm.trans (h.2.trans (cs a d))⟩
    let R := RedPlus G c
    have rs {a b : V} (h : R a b) : R b a := by
      refine ⟨sym h.1, ?_⟩
      rcases h.2 with h|h
      · exact Or.inl ((cs a b).symm.trans h)
      · exact Or.inr (Erdős151.lone_symm (G := G) sym h)
    have ri a (h : R a a) := irr a h.1
    have rt : Erdos151Ramsey.TriangleFree R := redPlus_triangleFree G c sym va
    obtain ⟨T,ht,hind⟩ := H R rs ri rt
    exact ⟨T,ht,independent_redPlus_free G c va (T : Set V) hind⟩

#print axioms ramsey_has_free_ten
#print axioms k4free_of_triangle_independent_ten
end Erdős151.H10
