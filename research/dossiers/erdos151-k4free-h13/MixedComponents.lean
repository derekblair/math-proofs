import ActualBookThreeSquare
import PetersenComponents

open scoped BigOperators
namespace H13MixedComponents
set_option linter.style.haveILetI false
open H13PetersenComponents Erdős151.H13 Erdős151.H12

/-- The simple graph induced on a component, with the actual same edges. -/
def componentGraph {V : Type*} (G : SimpleGraph V) (i : Component G.Adj) :
    SimpleGraph (Fiber G.Adj i) where
  Adj := induced G.Adj i
  symm := ⟨fun _ _ h => G.adj_symm h⟩
  loopless := ⟨fun a h => G.irrefl (v := a.val) h⟩

def SquareAt {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∃ x : Fin 4 → V, Function.Injective x ∧
    (∀ j, G.Adj v (x j)) ∧ (∀ j, G.Adj (x j) (x (j+1)))

/-- Catalog-level conditions for a connected component. The order and
type of the local model may vary independently at every vertex. -/
structure MixedCertificate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  delete : LinkDeletionConnected G
  cut : ∀ v : V, ∀ U : Finset (Lk G v), U.Nonempty → (∃ j,j∉U) →
    3 ≤ ((U ×ˢ (Finset.univ \ U)).filter (fun a => G.Adj a.1.val a.2.val)).card
  book : ∀ e : Edges G,
    (∑ t : Triangles G, if e ∈ incidentTriangles G t then (1:ℕ) else 0) = 3
  kind : ∀ v,
    SquareAt G v ∨ (∃ iso : Lk G v ≃ Fin 10,
      ∀ a b, G.Adj a.val b.val ↔ PetersenAdj (iso a) (iso b))

noncomputable def defaultEq {V : Type*} : DecidableEq V := Classical.decEq V

/-- Non-Ramsey is a componentwise property. -/
theorem nonRamsey_of_components {V : Type*} (G : V → V → Prop)
    (pieces : ∀ i : Component G, ¬ BikovLocal.Ramsey (induced G i)) :
    ¬ BikovLocal.Ramsey G := by
  classical
  have good (i : Component G) : ∃ c : Fiber G i → Fiber G i → Bool,
      (∀ a b, c a b = c b a) ∧ BikovLocal.Safe (induced G i) c := by
    by_contra hn
    apply pieces i
    intro c cs hc
    exact hn ⟨c,cs,hc⟩
  choose F fs fg using good
  let g := fun a b : V => if h : comp G b = comp G a then
    F (comp G a) ⟨a,rfl⟩ ⟨b,h⟩ else false
  have coh (a b : V) (i : Component G) (ha : comp G a=i) (hb : comp G b=i) :
      g a b = F i ⟨a,ha⟩ ⟨b,hb⟩ := by
    subst i
    simp [g,hb]
  intro hr
  apply hr g
  · intro a b
    by_cases he : comp G a = comp G b
    · rw [coh a b (comp G a) rfl he.symm,coh b a (comp G a) he.symm rfl]
      exact fs _ _ _
    · simp [g,he,Ne.symm he]
  · intro a b c hab hbc hac
    have eb := (comp_eq_of_edge G hab).symm
    have ec := comp_eq_of_edge G hac
    rw [coh a b (comp G a) rfl eb,coh b c (comp G a) eb ec,coh c a (comp G a) ec rfl]
    exact fg _ _ _ _ hab hbc hac

@[instance_reducible] noncomputable def componentFinite {V : Type*} [Fintype V] (G : SimpleGraph V)
    (i : Component G.Adj) : Fintype (Fiber G.Adj i) := Fintype.ofFinite _

/-- If every edge-bearing component has neutral cubic local certificates,
the square-vs-Petersen branch closes the coloring. Hall is an explicit
external hypothesis only in the pure Petersen branch. -/
theorem mixed_nonRamsey {V : Type u} [Fintype V] (G : SimpleGraph V)
    (size : Fintype.card V ≤ 63) (hall : HallProjection63.{u})
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
    · have hs : Fintype.card (Fiber G.Adj i) ≤ 63 :=
        (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans size
      apply nonRamsey_of_locallyPetersen63 hall H.Adj hs
        (fun {_ _} h => H.adj_symm h) (fun a h => H.irrefl (v:=a) h)
      intro v _
      exact (C.kind v).resolve_left (fun h => sq ⟨v,h⟩)
  · intro bad
    apply bad (fun _ _ => false) (by intro a b; rfl)
    intro a b c hab
    exact (h ⟨a,b,hab⟩).elim

#print axioms nonRamsey_of_components
#print axioms mixed_nonRamsey
end H13MixedComponents
