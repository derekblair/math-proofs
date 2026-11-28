import HubSpecial
import RamseyExactNine

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey

def alphaFloorFour (m : ℕ) : ℕ := if 9 ≤ m then 4 else alphaFloor m

def outerFloor (a b s : ℕ) : ℕ :=
  max (alphaFloorFour (14-a-b-s))
    (max (alphaFloor (7-a-s)+alphaFloor (7-b-s))
      (if s=1 ∧ a≤4 ∧ b≤4 then 3 else 0))

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem outer_from_chart
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G)
    (sub : ∀ a b, C a b → G a b) (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (rx : 8 ≤ (neighbors C x).card) (ry : 8 ≤ (neighbors C y).card) :
    let a := (neighbors G x∩neighbors G w).card
    let b := (neighbors G y∩neighbors G w).card
    let s := ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
    ∃ B ⊆ outerCandidates G x w y,
      outerFloor a b s ≤ B.card ∧ Independent (pairConflict G x y) B := by
  classical
  let a := (neighbors G x∩neighbors G w).card
  let b := (neighbors G y∩neighbors G w).card
  let s := ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
  let E := outerCandidates G x w y
  let P := pairConflict G x y
  have ob := outer_candidates_size G C sub coreNonlone x w y
  change _ ≤ E.card+s+a+b+2 at ob
  have xb := exclusive_core_side_size G C sub x w y
  change _ ≤ (exclusiveCoreSide G C x w y).card + a+s+1 at xb
  have yb := exclusive_core_side_size G C sub y w x
  rw [Finset.inter_comm (neighbors G y) (neighbors G x)] at yb
  change _ ≤ (exclusiveCoreSide G C y w x).card + b+s+1 at yb
  have odx := outer_core_side_size G C sub x w
  have ody := outer_core_side_size G C sub y w
  change _ ≤ (outerCoreSide G C x w).card + a + 1 at odx
  change _ ≤ (outerCoreSide G C y w).card + b + 1 at ody
  have union : ∃ B ⊆ E, alphaFloorFour (14-a-b-s) ≤ B.card ∧ Independent P B := by
    by_cases h : 9 ≤ 14-a-b-s
    · rw [alphaFloorFour, if_pos h]
      exact independent_four_of_nine P (conflict_symm G sym x y) (conflict_irr G irr x y)
        (pairConflict_triangleFree G x y link) E (by omega)
    · rw [alphaFloorFour, if_neg h]
      exact choose_alpha_floor P E (14-a-b-s) (by omega) (conflict_symm G sym x y)
        (conflict_irr G irr x y) (pairConflict_triangleFree G x y link)
  have sep := independent_from_exclusive G C sym irr link sub coreNonlone
      x w y (7-a-s) (7-b-s) (by omega) (by omega)
  have shared : ∃ B ⊆ E, (if s=1 ∧ a≤4 ∧ b≤4 then 3 else 0) ≤ B.card ∧ Independent P B := by
    split_ifs with h
    · exact shared_one_outer_three G C sym irr link sub coreNonlone x w y
        (by omega) (by omega) (by omega) (by omega) h.1
    · exact ⟨∅,Finset.empty_subset _,by simp,by simp [Independent]⟩
  change ∃ B ⊆ E, outerFloor a b s ≤ B.card ∧ Independent P B
  unfold outerFloor
  rcases le_total (alphaFloorFour (14-a-b-s))
      (max (alphaFloor (7-a-s)+alphaFloor (7-b-s)) (if s=1 ∧ a≤4 ∧ b≤4 then 3 else 0)) with h|h
  · rw [max_eq_right h]
    rcases le_total (alphaFloor (7-a-s)+alphaFloor (7-b-s))
      (if s=1 ∧ a≤4 ∧ b≤4 then 3 else 0) with h|h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  · rwa [max_eq_left h]

/-- The exact three-hub chart comparator gives a true ambient free set.
The hypotheses record the actual ambient prices and the chart's retained
center witness; they do not treat an induced picture as the whole graph. -/
theorem free13_of_chart_price
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b) (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (cxw : C x w) (cyw : C y w) (hxy : ¬ G x y) (xyne : x ≠ y)
    (rx : 8 ≤ (neighbors C x).card) (ry : 8 ≤ (neighbors C y).card)
    (A : Finset V) (aM : A ⊆ centerCandidates G C x w y) (ia : Independent G A)
    (price : let a := (neighbors G x∩neighbors G w).card
      let b := (neighbors G y∩neighbors G w).card
      let s := ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
      (neighbors G x).card + (neighbors G y).card + (neighbors G w).card + 40 ≤
        Fintype.card V + a + b + s + A.card + outerFloor a b s) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  obtain ⟨B,bE,bcard,ib⟩ := outer_from_chart G C sym irr link sub coreNonlone x w y rx ry
  have hxw := sub x w cxw
  have hyw := sub y w cyw
  have dis := (candidate_pools_disjoint G C sub x w y).mono aM bE
  apply free13_of_three_hub_budget G sym irr link R41 x w y hxw (sym hyw) hxy xyne
    (coreNonlone x w cxw) (coreNonlone y w cyw) A B
    (fun u hu => center_candidates_eligible G C sub coreNonlone x w y u (aM hu))
    (fun u hu => outer_candidates_eligible G x w y u (bE hu)) ia ib
  · intro u hu
    have h : u ∈ centerCandidates G C x w y ∪ outerCandidates G x w y :=
      (Finset.mem_union.mp hu).elim (fun h => Finset.mem_union_left _ (aM h))
        (fun h => Finset.mem_union_right _ (bE h))
    exact candidate_pools_inside G C sub irr x w y (sym hxw) (sym hyw) h
  · rw [Finset.card_union_of_disjoint dis]
    dsimp only at price bcard
    omega

#print axioms free13_of_chart_price
end Erdos151H13
