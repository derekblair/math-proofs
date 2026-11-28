import H13KneserColor
import Mathlib.Logic.Relation

namespace H13PetersenComponents

/-- Connected-component index; the equivalence closure permits using
an arbitrary orientation for the raw graph adjacency. -/
abbrev Component {V : Type*} (G : V → V → Prop) :=
  Quotient (Relation.EqvGen.setoid G)

def comp {V : Type*} (G : V → V → Prop) (v : V) : Component G :=
  Quotient.mk _ v

theorem comp_eq_of_edge {V : Type*} (G : V → V → Prop)
    {a b : V} (hab : G a b) : comp G a = comp G b :=
  Quotient.sound (Relation.EqvGen.rel _ _ hab)

/-- Piecewise assembly of homomorphisms. No proof of global connectedness
is needed, and all fibers can share the same target. -/
theorem assemble {V W I : Type*} (G : V → V → Prop) (H : W → W → Prop)
    (idx : V → I) (constant : ∀ a b, G a b → idx a = idx b)
    (pieces : ∀ i, ∃ f : {v : V // idx v = i} → W,
      ∀ a b, G a.val b.val → H (f a) (f b)) :
    ∃ f : V → W, ∀ a b, G a b → H (f a) (f b) := by
  classical
  choose F hF using pieces
  let g := fun v : V => F (idx v) ⟨v,rfl⟩
  have cohere (v : V) (i : I) (hv : idx v = i) : g v = F i ⟨v,hv⟩ := by
    subst i
    rfl
  refine ⟨g,?_⟩
  intro a b h
  have equal := constant a b h
  rw [cohere a (idx a) rfl, cohere b (idx a) equal.symm]
  exact hF (idx a) ⟨a,rfl⟩ ⟨b,equal.symm⟩ h

/-- The exact endpoint needed to use an external local-recognition theorem:
only the existence of an adjacency-preserving map on each component is
assumed. This theorem does not formalize Hall's classification. -/
theorem nonRamsey_of_component_kneser {V : Type*} (G : V → V → Prop)
    (pieces : ∀ i : Component G, ∃ f : {v : V // comp G v = i} → Fin 21,
      ∀ a b, G a.val b.val → Erdos151H13.Kneser.Adj (f a) (f b)) :
    ¬ BikovLocal.Ramsey G := by
  obtain ⟨f,hf⟩ := assemble G Erdos151H13.Kneser.Adj (comp G)
    (fun _ _ hab => comp_eq_of_edge G hab) pieces
  exact Erdos151H13.Kneser.pullback_color G f (fun {a b} hab => hf a b hab)

#print axioms assemble
#print axioms nonRamsey_of_component_kneser

/-- Components carrying no edge need no recognition theorem. -/
theorem nonRamsey_of_nontrivial_component_kneser {V : Type*} (G : V → V → Prop)
    (pieces : ∀ i : Component G,
      (∃ a b : {v : V // comp G v = i}, G a.val b.val) →
      ∃ f : {v : V // comp G v = i} → Fin 21,
        ∀ a b, G a.val b.val → Erdos151H13.Kneser.Adj (f a) (f b)) :
    ¬ BikovLocal.Ramsey G := by
  classical
  apply nonRamsey_of_component_kneser G
  intro i
  by_cases h : ∃ a b : {v : V // comp G v = i}, G a.val b.val
  · exact pieces i h
  · exact ⟨fun _ => 0, fun a b hab => (h ⟨a,b,hab⟩).elim⟩

#print axioms nonRamsey_of_nontrivial_component_kneser

def PetersenMask (a : Fin 10) : Nat :=
  (#[3,5,9,17,6,10,18,12,20,24] : Array Nat)[a.val]!

def PetersenAdj (a b : Fin 10) : Prop :=
  PetersenMask a &&& PetersenMask b = 0

/-- The Petersen graph here is the Kneser graph on 2-subsets of five
points. Every actual neighbor-subtype link is required isomorphic to it. -/
def LocallyPetersen {V : Type*} (G : V → V → Prop) : Prop :=
  ∀ v, ∃ iso : {w : V // G v w} ≃ Fin 10,
    ∀ a b, G a.val b.val ↔ PetersenAdj (iso a) (iso b)

abbrev Fiber {V : Type*} (G : V → V → Prop) (i : Component G) :=
  {v : V // comp G v = i}

abbrev induced {V : Type*} (G : V → V → Prop) (i : Component G)
    (a b : Fiber G i) : Prop := G a.val b.val

theorem induced_connected {V : Type*} (G : V → V → Prop) (i : Component G) :
    ∀ a b : Fiber G i, Relation.EqvGen (induced G i) a b := by
  have lift {a b : V} (h : Relation.EqvGen G a b) :
      ∀ (ha : comp G a = i) (hb : comp G b = i),
        Relation.EqvGen (induced G i) ⟨a,ha⟩ ⟨b,hb⟩ := by
    induction h with
    | rel a b h => exact fun ha hb => Relation.EqvGen.rel _ _ h
    | refl a => exact fun ha hb => Relation.EqvGen.refl _
    | symm a b _ ih =>
      exact fun hb ha => Relation.EqvGen.symm _ _ (ih ha hb)
    | trans a b c h₁ _ ih₁ ih₂ =>
      intro ha hc
      have hb : comp G b = i := (Quotient.sound h₁).symm.trans ha
      exact Relation.EqvGen.trans _ ⟨b,hb⟩ _ (ih₁ ha hb) (ih₂ hb hc)
  intro a b
  exact lift (Quotient.exact (a.property.trans b.property.symm)) a.property b.property

/-- Inducing on a component does not change the link of any of its
vertices: every edge preserves the component index. -/
def neighborEquiv {V : Type*} (G : V → V → Prop)
    (i : Component G) (v : Fiber G i) :
    {w : Fiber G i // induced G i v w} ≃ {w : V // G v.val w} where
  toFun w := ⟨w.val.val,w.property⟩
  invFun w := ⟨⟨w.val,(comp_eq_of_edge G w.property).symm.trans v.property⟩,w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem locallyPetersen_component {V : Type*} (G : V → V → Prop)
    (i : Component G) (h : LocallyPetersen G) : LocallyPetersen (induced G i) := by
  intro v
  obtain ⟨iso,hi⟩ := h v.val
  exact ⟨(neighborEquiv G i v).trans iso, fun a b =>
    hi (neighborEquiv G i v a) (neighborEquiv G i v b)⟩

universe u

/-- Explicit EXTERNAL input: the needed consequence of Hall's
local-recognition theorem; not introduced as an axiom.
Cohen's exposition identifies the 21-vertex KG(7,2), its 63-vertex
triple cover, and the excluded 65-vertex Doro graph. -/
def HallProjection63 : Prop :=
  ∀ (V : Type u) [Fintype V] (G : V → V → Prop),
    Fintype.card V ≤ 63 → BikovLocal.Sym G → BikovLocal.Loopless G →
    (∀ a b, Relation.EqvGen G a b) → LocallyPetersen G →
    ∃ f : V → Fin 21, ∀ a b, G a b → Erdos151H13.Kneser.Adj (f a) (f b)

/-- Finite core-coloring adapter: no global connectedness requirement,
and isolated vertices need not have a Petersen link. -/
theorem nonRamsey_of_locallyPetersen63 {V : Type u} [Fintype V]
    (hall : HallProjection63.{u}) (G : V → V → Prop)
    (size : Fintype.card V ≤ 63) (sym : BikovLocal.Sym G) (irr : BikovLocal.Loopless G)
    (localPet : ∀ v, (∃ w,G v w) →
      ∃ iso : {w : V // G v w} ≃ Fin 10,
        ∀ a b, G a.val b.val ↔ PetersenAdj (iso a) (iso b)) :
    ¬ BikovLocal.Ramsey G := by
  classical
  apply nonRamsey_of_nontrivial_component_kneser G
  intro i hi
  have support (a : Fiber G i) : ∃ b : V, G a.val b := by
    by_contra h
    have isolated : ∀ b, ¬ G a.val b := fun b hb => h ⟨b,hb⟩
    obtain ⟨x,y,edge⟩ := hi
    have only {v w : V} (p : Relation.EqvGen G v w) : v=a.val ↔ w=a.val := by
      induction p with
      | rel v w h =>
        exact ⟨fun e => (isolated w (e ▸ h)).elim,
          fun e => (isolated v (e ▸ (sym h))).elim⟩
      | refl v => rfl
      | symm v w _ ih => exact ih.symm
      | trans v w z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have xx := (only (Quotient.exact (a.property.trans x.property.symm))).mp rfl
    exact isolated y.val (xx ▸ edge)
  letI : Fintype (Fiber G i) := Fintype.ofFinite _
  have small : Fintype.card (Fiber G i) ≤ 63 :=
    (Fintype.card_le_of_injective (fun v : Fiber G i => v.val) Subtype.val_injective).trans size
  apply hall (Fiber G i) (induced G i) small
  · exact fun {a b} h => sym h
  · exact fun a h => irr a.val h
  · exact induced_connected G i
  · intro v
    obtain ⟨iso,hi⟩ := localPet v.val (support v)
    exact ⟨(neighborEquiv G i v).trans iso, fun a b =>
      hi (neighborEquiv G i v a) (neighborEquiv G i v b)⟩

#print axioms nonRamsey_of_locallyPetersen63
end H13PetersenComponents
