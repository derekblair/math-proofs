import H12FiveCut

namespace Erdos151H12
open Erdős151
variable {V : Type*} [DecidableEq V] [Fintype V] (G C : V → V → Prop)
variable [DecidableRel G] [DecidableRel C]

theorem core_book_le_ambient (mono : ∀ {a b}, C a b → G a b) (u v : V) :
    ambientCodeg C u v ≤ ambientCodeg G u v := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hu,hv⟩ := Finset.mem_inter.mp hx
  exact Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr (mono ((mem_neighbors C).mp hu)),
    (mem_neighbors G).mpr (mono ((mem_neighbors C).mp hv))⟩

theorem core_edge_budgets
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (symC : ∀ {a b}, C a b → C b a) (tf : TriangleFreeLinks G)
    (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C)
    (lower : ∀ R : Finset V, 41 ≤ R.card →
      ∃ P ⊆ R, 10 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (cap8 : ∀ u v, C u v → (neighbors C u).card = 8 → ambientCodeg C u v ≤ 4)
    (u v : V) (huv : C u v) (hu8 : 8 ≤ (neighbors C u).card) (hv8 : 8 ≤ (neighbors C v).card) :
    let r := (neighbors C u).card
    let s := (neighbors C v).card
    let a := (neighbors G u).card
    let b := (neighbors G v).card
    let n := Fintype.card V
    n ≤ 34+a+b ∧
    (40+a+b ≤ n+6 → r=8 ∧ s=8 ∧ ambientCodeg C u v = 2) ∧
    (40+a+b ≤ n+7 → ambientCodeg C u v ≤ 3) ∧
    (40+a+b ≤ n+7 → (10 ≤ r ∨ 10 ≤ s) → ambientCodeg C u v = 2) := by
  dsimp
  have h := adjacent_core_necessary (G:=G) (C:=C) sym irr symC tf mono t lower upper u v huv
  have ha := core_overlap_has_two G C mono t u v huv
  have hc := core_overlap_has_two C C (fun e => e) t u v huv
  have hcc := core_book_le_ambient G C mono u v
  have h6 := twoHubFloor_ge_six _ _ _ hu8 hv8 ha
  refine ⟨by omega,?_,?_,?_⟩
  · intro bud
    have hlim : twoHubFloor (neighbors C u).card (neighbors C v).card (ambientCodeg G u v) ≤ 6 := by omega
    obtain ⟨h2,hr,hs⟩ := twoHubFloor_le_six _ _ _ hu8 hv8 ha hlim
    exact ⟨hr,hs,by omega⟩
  · intro bud
    have hlim : twoHubFloor (neighbors C u).card (neighbors C v).card (ambientCodeg G u v) ≤ 7 := by omega
    rcases twoHubFloor_le_seven _ _ _ hu8 hv8 ha hlim with h2|h3|h5
    · omega
    · omega
    · have hx := tight_five_core_codegree G C sym irr symC tf mono t lower upper
        u v huv hu8 hv8 h5.1 bud
      have hz := cap8 u v huv h5.2.1
      omega
  · intro bud hhigh
    have hlim : twoHubFloor (neighbors C u).card (neighbors C v).card (ambientCodeg G u v) ≤ 7 := by omega
    rcases twoHubFloor_le_seven _ _ _ hu8 hv8 ha hlim with h2|h3|h5
    · omega
    · omega
    · omega

#print axioms core_edge_budgets
end Erdos151H12
