import HubSpecial
import HubWide

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

/-- Full three-hub retention step at order at least 64: either two
4-heavy rim books or a 4-heavy/3-heavy pair with two common neighbors
in the center link. This checks the actual graph, not a scalar model. -/
theorem three_hub_free13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (cxw : C x w) (cyw : C y w) (hxy : ¬ G x y) (xyne : x ≠ y)
    (rx : 8 ≤ (neighbors C x).card) (ry : 8 ≤ (neighbors C y).card)
    (rw9 : 9 ≤ (neighbors C w).card)
    (n : 64 ≤ Fintype.card V)
    (D : (neighbors G x).card + (neighbors G y).card + (neighbors G w).card ≤ 36)
    (a4 : 4 ≤ (neighbors G x∩neighbors G w).card)
    (b3 : 3 ≤ (neighbors G y∩neighbors G w).card)
    (mix : 4 ≤ (neighbors G y∩neighbors G w).card ∨
       2 ≤ ((neighbors G x∩neighbors G w)∩(neighbors G y∩neighbors G w)).card) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  let a := (neighbors G x∩neighbors G w).card
  let b := (neighbors G y∩neighbors G w).card
  let s := ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
  let t := ((neighbors G x∩neighbors G w)∩(neighbors G y∩neighbors G w)).card
  by_cases wide : 10 ≤ a+b+s
  · exact wide_three_hub_free13 G C sym irr link R41 sub coreNonlone
      x w y cxw cyw hxy xyne rx ry n D wide
  let E := outerCandidates G x w y
  let M := centerCandidates G C x w y
  let P := pairConflict G x y
  have hxw := sub x w cxw
  have hyw := sub y w cyw
  have ob := outer_candidates_size G C sub coreNonlone x w y
  change _ ≤ E.card + s + a + b + 2 at ob
  have cb := center_candidates_size G C x w y
  change _ + t ≤ M.card + a+b+2 at cb
  have xb := exclusive_core_side_size G C sub x w y
  change _ ≤ _ + a+s+1 at xb
  have yb := exclusive_core_side_size G C sub y w x
  rw [Finset.inter_comm (neighbors G y) (neighbors G x)] at yb
  change _ ≤ _ + b+s+1 at yb
  have centerTF : TriangleFree (fun u v : ↥M => G u.val v.val) := by
    intro i j k ij jk ik
    have hw (u : ↥M) : G w u.val :=
      (center_candidates_eligible G C sub coreNonlone x w y _ u.property).1
    exact link w i.val j.val k.val (hw i) (hw j) (hw k) ij jk ik
  have pickCenter : ∃ A ⊆ M, alphaFloor (7+t-a-b) ≤ A.card ∧ Independent G A := by
    let g : ↥M → ↥M → Prop := fun i j => G i.val j.val
    obtain ⟨S,_,hs,hi⟩ := choose_alpha_floor g Finset.univ (7+t-a-b)
      (by rw [Finset.card_univ,Fintype.card_coe]; omega)
      (fun {_ _} h => sym h) (fun i => irr i.val) centerTF
    let emb : ↥M ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    refine ⟨S.map emb,?_,by simpa only [Finset.card_map] using hs,?_⟩
    · intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
      exact w.property
    · intro u hu v hv
      obtain ⟨i,hi',rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j,hj',rfl⟩ := Finset.mem_map.mp hv
      exact hi i hi' j hj'
  have assemble (A B : Finset V) (aM : A ⊆ M) (bE : B ⊆ E)
      (ia : Independent G A) (ib : Independent P B)
      (cap : 12 ≤ a+b+s+A.card+B.card) :
      ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
    have dis := (candidate_pools_disjoint G C sub x w y).mono aM bE
    apply free13_of_three_hub_budget G sym irr link R41 x w y hxw (sym hyw) hxy xyne
      (coreNonlone x w cxw) (coreNonlone y w cyw) A B
      (fun u hu => center_candidates_eligible G C sub coreNonlone x w y u (aM hu))
      (fun u hu => outer_candidates_eligible G x w y u (bE hu)) ia ib
    · intro u hu
      have u' : u ∈ M ∪ E := Finset.mem_union.mp hu |>.elim
        (fun h => Finset.mem_union_left _ (aM h)) (fun h => Finset.mem_union_right _ (bE h))
      exact candidate_pools_inside G C sub irr x w y (sym hxw) (sym hyw) u'
    · rw [Finset.card_union_of_disjoint dis]
      change _ ≤ Fintype.card V + a+b+s+(A.card+B.card)
      omega
  obtain ⟨A,asub,ac,ia⟩ := pickCenter
  have recipes := thin_overlap_recipe a b s t a4 b3 mix (by omega)
  rcases recipes with r|r|⟨r1,r2,r3⟩
  · obtain ⟨B,bs,bc,ib⟩ := choose_alpha_floor P E (14-a-b-s) (by omega)
      (conflict_symm G sym x y) (conflict_irr G irr x y) (pairConflict_triangleFree G x y link)
    exact assemble A B asub bs ia ib (by omega)
  · obtain ⟨B,bs,bc,ib⟩ := independent_from_exclusive G C sym irr link sub coreNonlone
      x w y (7-a-s) (7-b-s) (by omega) (by omega)
    exact assemble A B asub bs ia ib (by omega)
  · have odx := outer_core_side_size G C sub x w
    have ody := outer_core_side_size G C sub y w
    change _ ≤ _ + a + 1 at odx
    change _ ≤ _ + b + 1 at ody
    obtain ⟨B,bs,bc,ib⟩ := shared_one_outer_three G C sym irr link sub coreNonlone x w y
        (by omega) (by omega) (by omega) (by omega) r3
    exact assemble A B asub bs ia ib (by omega)

#print axioms three_hub_free13
end Erdos151H13
