import H10Outside
import H10Upper
import H10Unblocked
import H10Arithmetic
import UnblockingExterior

namespace Erdős151.H10
open Upper
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem h10_outside_stage_lower {G : V → V → Prop}
    [DecidableRel G] [DecidableRel (Lone G)]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G) (cap : FreeCap G 9) (w : V) :
    let S := nbr G w
    let n := Fintype.card V
    let I := incidence G S (ext S w)
    let L := incidence (Lone G) S (ext S w)
    (S.card = 9 → 12*(n-10) ≤ 4*I+54+2*L) ∧
    (S.card = 8 → L=0 → 6*(n-12) ≤ 2*I+40) := by
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
  have hlo := h10_outside_lower (G := G) sym irr link cap S E de hs hb
  obtain ⟨hi,hl⟩ := sub_incidence (G := G) sym S E X se
  change (S.card = 9 → 12*(Fintype.card V-10) ≤
    4*incidence G S X+54+2*incidence (Lone G) S X) ∧
    (S.card = 8 → incidence (Lone G) S X=0 →
    6*(Fintype.card V-12) ≤ 2*incidence G S X+40)
  refine ⟨?_,?_⟩
  · intro hd
    have hu := unblocked_stage_nine (G := G) sym cap S U du hs ha hd
    have h := hlo.1 hd
    omega
  · intro hd hz
    have hu := unblocked_stage_eight (G := G) sym cap link S U du hs ha hd
    have he : (∑ x ∈ E, (ls (G := G) S x).card) = 0 := by omega
    have h := hlo.2 hd he
    omega

theorem h10_exclude_core {G C : V → V → Prop}
    [DecidableRel G] [DecidableRel C] [DecidableRel (Lone G)]
    (sym : ∀ {a b}, G a b → G b a) (symC : ∀ {a b}, C a b → C b a)
    (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G) (cap : FreeCap G 9)
    (sub : ∀ {a b}, C a b → G a b) (hn : 36 ≤ Fintype.card V)
    (coreMin : ∀ u, (nbr C u).Nonempty → 8 ≤ (nbr C u).card)
    (book : ∀ u, ∀ v ∈ nbr C u, 2 ≤ ((nbr C u).filter (C v)).card)
    (w : V) (hw : (nbr C w).Nonempty) : False := by
  have deg (u : V) : (nbr G u).card ≤ 9 := by
    apply cap
    have hSet : (↑(nbr G u) : Set V) = {v | G u v} := by ext v; simp [nbr]
    rw [hSet]
    exact neighborhood_free G sym link u
  have leD (u : V) : (nbr C u).card ≤ (nbr G u).card :=
    Finset.card_le_card (fun v hv =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub (Finset.mem_filter.mp hv).2⟩)
  have Cnext (u j : V) (hj : j ∈ nbr C u) : (nbr C j).Nonempty :=
    ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,symC (Finset.mem_filter.mp hj).2⟩⟩
  have nn (u : V) (hu : (nbr C u).Nonempty) : (nbr G u).card ≤ 8 := by
    by_contra h
    have hd : (nbr G u).card = 9 := by have hh := deg u; omega
    have hlow := (h10_outside_stage_lower (G := G) sym irr link cap u).1 hd
    have hi := edge_budget_h10 G C sym sub u (irr u) 9 (fun j _ => deg j)
      (fun j _ => deg j) (book u)
    have hl := lone_budget_h10 G C sym sub u (irr u) 9 (fun j _ => deg j)
      (fun j _ => deg j) (fun j hj => coreMin j (Cnext u j hj)) (core_not_lone G C sub book)
    have rlo := coreMin u hu
    have cle := leD u
    omega
  have hd : (nbr G w).card = 8 := by have := nn w hw; have := coreMin w hw; have := leD w; omega
  have hr : (nbr C w).card = 8 := by have := coreMin w hw; have := leD w; omega
  have hi := edge_budget_h10 G C sym sub w (irr w) 8 (fun j _ => deg j)
    (fun j hj => nn j (Cnext w j hj)) (book w)
  have hl := lone_budget_h10 G C sym sub w (irr w) 8 (fun j _ => deg j)
    (fun j hj => nn j (Cnext w j hj)) (fun j hj => coreMin j (Cnext w j hj))
    (core_not_lone G C sub book)
  have hz : incidence (Lone G) (nbr G w) (ext (nbr G w) w) = 0 := by omega
  have hlow := (h10_outside_stage_lower (G := G) sym irr link cap w).2 hd hz
  omega

#print axioms h10_outside_stage_lower
#print axioms h10_exclude_core
end Erdős151.H10
