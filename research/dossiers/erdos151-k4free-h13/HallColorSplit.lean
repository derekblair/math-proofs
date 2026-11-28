import PetersenComponents
import Hall65Color

namespace H13PetersenComponents
universe u

/-- The published three-case Hall recognition theorem, phrased as the
weakest edge-preserving map conclusion used by the color proof. The
21-vertex model and its triple cover map to KG(7,2); the 65-vertex model
maps to the explicit Hall graph. This declaration is a proposition,
not an axiom. -/
def HallProjectionAll : Prop :=
  ∀ (V : Type u) [Fintype V] (G : V → V → Prop),
    BikovLocal.Sym G → BikovLocal.Loopless G →
    (∀ a b, Relation.EqvGen G a b) → LocallyPetersen G →
    (∃ f : V → Fin 21, ∀ a b, G a b → Erdos151H13.Kneser.Adj (f a) (f b)) ∨
    (∃ f : V → Fin 65, ∀ a b, G a b → Erdos151H13.Hall65.Adj (f a) (f b))

theorem pullback_hall65_color {V : Type*} (G : V → V → Prop) (f : V → Fin 65)
    (hf : ∀ a b, G a b → Erdos151H13.Hall65.Adj (f a) (f b)) :
    ¬ BikovLocal.Ramsey G := by
  intro h
  let c (a b : V) := Erdos151H13.Hall65.color (f a) (f b)
  apply h c (fun a b=>Erdos151H13.Hall65.color_symmetric (f a) (f b))
  intro a b t ab bt ta mono
  have x := List.all_eq_true.mp (Erdos151H13.Hall65.safe_computed (f a)) (f b) (List.mem_finRange _)
  have y1 := hf a b ab
  have y2 := hf b t bt
  have y3 := hf t a ta
  change Erdos151H13.Hall65.adjBool (f a) (f b) = true at y1
  change Erdos151H13.Hall65.adjBool (f b) (f t) = true at y2
  change Erdos151H13.Hall65.adjBool (f t) (f a) = true at y3
  simp only [y1,Bool.not_true,Bool.false_or] at x
  have y := List.all_eq_true.mp x (f t) (List.mem_finRange _)
  simp [y2,y3,c,mono.1,mono.2] at y

theorem nonRamsey_connected_locallyPetersen
    {V : Type u} [Fintype V] (G : V → V → Prop)
    (hall : HallProjectionAll.{u}) (sym : BikovLocal.Sym G) (irr : BikovLocal.Loopless G)
    (conn : ∀ a b, Relation.EqvGen G a b) (localPet : LocallyPetersen G) :
    ¬ BikovLocal.Ramsey G := by
  rcases hall V G sym irr conn localPet with ⟨f,hf⟩|⟨f,hf⟩
  · exact Erdos151H13.Kneser.pullback_color G f (fun {a b} h => hf a b h)
  · exact pullback_hall65_color G f hf

#print axioms nonRamsey_connected_locallyPetersen
end H13PetersenComponents
