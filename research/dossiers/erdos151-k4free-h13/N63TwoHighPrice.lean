import N63ActualLink

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey

private theorem short_high_pair : ∀ a b : Fin 3, ∀ s : Fin 3,
    13 ≤ (a.val+4)+(b.val+4)+s.val+2+outerFloor (a.val+4) (b.val+4) s.val := by decide

theorem high_pair_price (a b s : ℕ) (ha : 4≤a) (hb : 4≤b) :
    13 ≤ a+b+s+2+outerFloor a b s := by
  by_cases h : 11 ≤ a+b+s
  · omega
  · let i : Fin 3 := ⟨a-4,by omega⟩
    let j : Fin 3 := ⟨b-4,by omega⟩
    let k : Fin 3 := ⟨s,by omega⟩
    have ia : i.val+4=a := by change a-4+4=a; omega
    have jb : j.val+4=b := by change b-4+4=b; omega
    simpa only [ia,jb] using short_high_pair i j k

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem free13_of_two_high_center_two
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (Csym : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (cwx : C w x) (cwy : C w y) (hxy : ¬ G x y) (xyne : x ≠ y)
    (rx : 8 ≤ (neighbors C x).card) (ry : 8 ≤ (neighbors C y).card)
    (dx : 4 ≤ actualLinkDegree G C w x) (dy : 4 ≤ actualLinkDegree G C w y)
    (A : Finset V) (vA : ∀ v ∈ A, C w v ∧ v ≠ x ∧ v ≠ y ∧ ¬ G x v ∧ ¬ G y v)
    (ia : Independent G A) (ac : 2 ≤ A.card)
    (n : 63 ≤ Fintype.card V) (D : (neighbors G x).card + (neighbors G y).card + (neighbors G w).card ≤ 36) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  have a := actual_link_price_interval G C w x sub
  have b := actual_link_price_interval G C w y sub
  dsimp only at a b
  apply free13_of_chart_price G C sym irr link R41 sub coreNonlone x w y
    (Csym cwx) (Csym cwy) hxy xyne rx ry A (actual_center_witness G C w x y A sub vA) ia
  let c := (neighbors G x∩neighbors G w).card
  let d := (neighbors G y∩neighbors G w).card
  let s := ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
  have price := high_pair_price c d s (dx.trans a.1) (dy.trans b.1)
  change _ ≤ Fintype.card V + c + d + s + A.card + outerFloor c d s
  omega

#print axioms free13_of_two_high_center_two
end Erdos151H13
