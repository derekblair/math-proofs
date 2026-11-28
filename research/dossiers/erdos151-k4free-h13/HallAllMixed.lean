import MixedAnalyticFinished
import HallColorSplit

namespace H13MixedComponents
open H13PetersenComponents Erdős151.H13 Erdős151.H12 Erdős151.H12.Wagner
open Erdos151H12 Erdős151.Upper Erdos151CoreHigh Erdos151MarkedLinkTable

theorem mixed_nonRamsey_hall_all {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hall : HallProjectionAll.{u})
    (cert : ∀ i : Component G.Adj,
      (∃ a b : Fiber G.Adj i, G.Adj a.val b.val) →
      @MixedCertificate (Fiber G.Adj i) (componentFinite G i) defaultEq
        (componentGraph G i) (fun _ _ => Classical.propDecidable _)) :
    ¬ BikovLocal.Ramsey G.Adj := by
  classical
  apply nonRamsey_of_components
  intro i
  letI := componentFinite G i
  letI : DecidableEq (Fiber G.Adj i) := defaultEq
  let H := componentGraph G i
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  change ¬ BikovLocal.Ramsey H.Adj
  by_cases h : ∃ a b : Fiber G.Adj i, G.Adj a.val b.val
  · have C : MixedCertificate H := cert i h
    by_cases sq : ∃ v, SquareAt H v
    · obtain ⟨v,x,xi,sp,ri⟩ := sq
      have hconn : ∀ a b, Relation.ReflTransGen H.Adj a b := by
        letI : Std.Symm H.Adj := ⟨fun _ _ h => H.adj_symm h⟩
        intro a b
        rw [←Relation.EqvGen.eqvGen_eq_reflTransGen]
        exact induced_connected G.Adj i a b
      obtain ⟨c,cs,ok⟩ := actual_book_three_square_safe H hconn C.delete C.cut C.book v x xi sp ri
      exact fun bad => bad c cs ok
    · apply nonRamsey_connected_locallyPetersen H.Adj hall
        (fun {_ _} h => H.adj_symm h) (fun a h => H.irrefl (v:=a) h)
        (induced_connected G.Adj i)
      intro v
      exact (C.kind v).resolve_left (fun h => sq ⟨v,h⟩)
  · intro bad
    apply bad (fun _ _ => false) (by intro a b; rfl)
    intro a b c hab
    exact (h ⟨a,b,hab⟩).elim

theorem mixed_nonRamsey_of_templates_hall_all {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hall : HallProjectionAll.{u})
    (model : ∀ v, (∃ w,G.Adj v w) → HasTemplate G v) : ¬ BikovLocal.Ramsey G.Adj := by
  classical
  apply mixed_nonRamsey_hall_all G hall
  intro i hi
  letI := componentFinite G i
  letI : DecidableEq (Fiber G.Adj i) := defaultEq
  let H := componentGraph G i
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hh : ∀ v, HasTemplate H v := by
    intro v
    have hs : ∃ w, G.Adj v.val w := by
      by_contra no
      obtain ⟨a,b,edge⟩ := hi
      have isolated : ∀ w, ¬ G.Adj v.val w := fun w h => no ⟨w,h⟩
      have only {x y : V} (p : Relation.EqvGen G.Adj x y) : x=v.val ↔ y=v.val := by
        induction p with
        | rel x y h =>
          exact ⟨fun e => (isolated y (e ▸ h)).elim,
            fun e => (isolated x (e ▸ h.symm)).elim⟩
        | refl x => rfl
        | symm x y _ ih => exact ih.symm
        | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      have e := (only (Quotient.exact (v.property.trans a.property.symm))).mp rfl
      exact isolated b.val (e ▸ edge)
    obtain ⟨T,iso,valid⟩ := model v.val hs
    let equiv := neighborEquiv G.Adj i v
    exact ⟨T,equiv.trans iso,fun a b => valid (equiv a) (equiv b)⟩
  exact ⟨template_delete H hh,template_cut H hh,template_book H hh,template_kind H hh⟩


theorem nonRamsey_neutral_shapes_hall_all {V : Type u} [Fintype V] [DecidableEq V]
    (C : V→V→Prop) [DecidableRel C]
    (sym : BikovLocal.Sym C) (irr : BikovLocal.Loopless C)
    (tf : BikovLocal.TriangleFreeLinks C)
    (hall : HallProjectionAll.{u})
    (shapes : ∀ v, (neighbors C v).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) v, (edges L.kind).length=12) ∨
      ((neighbors C v).card=10 ∧ ∀ a∈neighbors C v,
        NineLinkPivot.deg C (neighbors C v) a=3)) :
    ¬ BikovLocal.Ramsey C := by
  have shaped : ∀ u, (neighbors C u).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) u, (edges L.kind).length=12) ∨
      (∀ v∈neighbors C u, ambientCodeg C u v=3) := by
    intro w hw
    rcases shapes w hw with h|⟨_,h⟩
    · exact Or.inl h
    · right
      intro a ha
      rw [←row_core_codeg C]
      exact h a ha
  have wagner := neutral_eight_is_wagner C (fun {_ _} h=>sym h) irr shaped
  apply mixed_nonRamsey_of_templates_hall_all (graphOf C sym irr) hall
  intro v hv
  obtain ⟨x,hx⟩ := hv
  rcases shapes v ⟨x,(mem_neighbors C).mpr hx⟩ with ⟨L,hL⟩|⟨r,h⟩
  · exact actual_wagner_template C sym irr v L (wagner v L hL)
  · exact actual_ten_template moore_ten_verified C sym irr tf v r h

#print axioms nonRamsey_neutral_shapes_hall_all
end H13MixedComponents
