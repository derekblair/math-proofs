import UnblockingOutside
import UnblockingExterior
import UnblockedCard

namespace Erdős151
open Upper
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem outside_stage_lower {G : V → V → Prop}
    [DecidableRel G] [DecidableRel (Lone G)]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G) (cap : FreeCap G 10) (w : V) :
    let S := nbr G w
    let n := Fintype.card V
    let I := incidence G S (ext S w)
    let L := incidence (Lone G) S (ext S w)
    (S.card = 10 → 12*(n-11) ≤ 4*I+60+2*L) ∧
    (S.card = 9 → 12*(n-13) ≤ 4*I+90+3*L) ∧
    (S.card = 8 → L=0 → 6*(n-18) ≤ 2*I+72) := by
  classical
  let S := nbr G w
  let X := ext S w
  let f := fun x => Free (Forbidden G) (insert x (S : Set V))
  let U := X.filter f
  let E := X.filter (fun x => ¬ f x)
  have hw : w ∉ S := fun hw => irr w (Finset.mem_filter.mp hw).2
  have hx := exterior_card S w hw
  change X.card = Fintype.card V - (S.card+1) at hx
  have hsplit : U.card+E.card = X.card := X.card_filter_add_card_filter_not f
  have dx : Disjoint S X := by
    apply Finset.disjoint_left.mpr
    intro u hu hx
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hu)
  have su : U ⊆ X := Finset.filter_subset _ _
  have se : E ⊆ X := Finset.filter_subset _ _
  have du : Disjoint S U :=
    Finset.disjoint_left.mpr (fun _ hu hv => Finset.disjoint_left.mp dx hu (su hv))
  have de : Disjoint S E :=
    Finset.disjoint_left.mpr (fun _ hu hv => Finset.disjoint_left.mp dx hu (se hv))
  have hs : Free (Forbidden G) (S : Set V) := by
    have hSet : (↑S : Set V) = {u | G w u} := by ext u; simp [S, nbr]
    rw [hSet]
    exact neighborhood_free G sym link w
  have ha : ∀ x ∈ U, f x := fun _ hx => (Finset.mem_filter.mp hx).2
  have hb : ∀ x ∈ E, ¬f x := fun _ hx => (Finset.mem_filter.mp hx).2
  have hlo := outside_lower (G := G) sym irr link cap S E de hs hb
  obtain ⟨hi,hl⟩ := sub_incidence (G := G) sym S E X se
  change (S.card = 10 → 12*(Fintype.card V-11) ≤
    4*incidence G S X+60+2*incidence (Lone G) S X) ∧
    (S.card = 9 → 12*(Fintype.card V-13) ≤
    4*incidence G S X+90+3*incidence (Lone G) S X) ∧
    (S.card = 8 → incidence (Lone G) S X=0 →
    6*(Fintype.card V-18) ≤ 2*incidence G S X+72)
  refine ⟨?_,?_,?_⟩
  · intro hd
    have hu := unblocked_stage_ten (G := G) sym cap S U du hs ha hd
    have h := hlo.1 hd
    omega
  · intro hd
    have hu := unblocked_stage_nine (G := G) sym cap link S U du hs ha hd
    have h := hlo.2.1 hd
    omega
  · intro hd hz
    have hu := unblocked_stage_eight (G := G) sym cap link S U du hs ha hd
    have he : (∑ x ∈ E, (ls (G := G) S x).card) = 0 := by omega
    have h := hlo.2.2 hd he
    omega

theorem exclude_core {G C : V → V → Prop}
    [DecidableRel G] [DecidableRel C] [DecidableRel (Lone G)]
    (sym : ∀ {a b}, G a b → G b a) (symC : ∀ {a b}, C a b → C b a)
    (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G) (cap : FreeCap G 10)
    (sub : ∀ {a b}, C a b → G a b) (hn : 47 ≤ Fintype.card V)
    (coreMin : ∀ u, (nbr C u).Nonempty → 8 ≤ (nbr C u).card)
    (book : ∀ u, ∀ v ∈ nbr C u, 2 ≤ ((nbr C u).filter (C v)).card)
    (w : V) (hw : (nbr C w).Nonempty) : False := by
  have deg (u : V) : (nbr G u).card ≤ 10 := neighborhood_cap (G := G) sym link cap u
  have rlo (u : V) (h : (nbr C u).Nonempty) : 8 ≤ (nbr G u).card := by
    have hh := coreMin u h
    have hsub : nbr C u ⊆ nbr G u := fun v hv =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub (Finset.mem_filter.mp hv).2⟩
    have := Finset.card_le_card hsub
    omega
  have Cnext (u j : V) (hj : j ∈ nbr C u) : (nbr C j).Nonempty :=
    ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,symC (Finset.mem_filter.mp hj).2⟩⟩
  have n10 (u : V) (hu : (nbr C u).Nonempty) : (nbr G u).card ≤ 9 := by
    by_contra h
    have hu10 : (nbr G u).card = 10 := by have hh := deg u; omega
    have rr := coreMin u hu
    have hlow := (outside_stage_lower (G := G) sym irr link cap u).1 hu10
    obtain ⟨hi,hl⟩ := stage_ten G C sym sub u (irr u) (fun j _ => deg j)
      (fun j hj => coreMin j (Cnext u j hj)) book hu10
    omega
  have n9 (u : V) (hu : (nbr C u).Nonempty) : (nbr G u).card ≤ 8 := by
    by_contra h
    have hu9 : (nbr G u).card = 9 := by have hh := n10 u hu; omega
    have rr := coreMin u hu
    have hlow := (outside_stage_lower (G := G) sym irr link cap u).2.1 hu9
    obtain ⟨hi,hl⟩ := stage_nine G C sym sub u (irr u) (fun j _ => deg j)
      (fun j hj => coreMin j (Cnext u j hj)) book hu9 (fun j hj => n10 j (Cnext u j hj))
    omega
  have hw8 : (nbr G w).card = 8 := by have := rlo w hw; have := n9 w hw; omega
  obtain ⟨hi,hl⟩ := stage_eight G C sym sub w (irr w) (fun j _ => deg j)
    (fun j hj => coreMin j (Cnext w j hj)) book hw8 (coreMin w hw)
    (fun j hj => n9 j (Cnext w j hj))
  have hlow := (outside_stage_lower (G := G) sym irr link cap w).2.2 hw8 hl
  omega

#print axioms outside_stage_lower
#print axioms exclude_core
end Erdős151
