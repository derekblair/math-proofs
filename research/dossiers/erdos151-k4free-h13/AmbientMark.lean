import AtlasHostTransport

namespace Erdos151H13
open Erdős151 Erdős151.H12 Erdos151H12

/-- A marking witnesses non-extendability even when the link graph is
not the core graph. The witness colors all pairs, so adding more
ambient edges cannot make the spoke constraints easier. -/
def MarkedRel {V : Type*} (G : V → V → Prop) : Prop :=
  ∃ color : V → V → Bool, (∀ a b, color a b = color b a) ∧
    ¬ ∃ f : V → Bool, ∀ a b, G a b → ¬ (f a = color a b ∧ f b = color a b)

theorem MarkedRel.mono {V : Type*} {C G : V → V → Prop}
    (sub : ∀ a b, C a b → G a b) (h : MarkedRel C) : MarkedRel G := by
  obtain ⟨c,cs,block⟩ := h
  refine ⟨c,cs,?_⟩
  rintro ⟨f,extend⟩
  exact block ⟨f,fun a b h => extend a b (sub a b h)⟩

theorem MarkedRel.transport {A B : Type*} (G : A → A → Prop)
    (slot : B ≃ A) (mark : MarkedRel G) :
    MarkedRel (fun a b => G (slot a) (slot b)) := by
  obtain ⟨c,cs,block⟩ := mark
  refine ⟨fun a b=>c (slot a) (slot b),fun a b=>cs _ _,?_⟩
  rintro ⟨f,h⟩
  apply block
  refine ⟨fun a => f (slot.symm a),?_⟩
  intro a b e
  have he : G (slot (slot.symm a)) (slot (slot.symm b)) := by simpa using e
  simpa using h (slot.symm a) (slot.symm b) he

/-- In a minimal Ramsey core, the induced ambient link on the actual
core neighbors is necessarily marked. This handles extra ambient edges
without assuming the ambient and core link are the same graph. -/
theorem ambient_core_link_marked {V : Type*} [Fintype V] [DecidableEq V]
    (C G : V → V → Prop) [DecidableRel C]
    (sub : BikovLocal.Sub C G) (sym : BikovLocal.Sym C) (irr : BikovLocal.Loopless C)
    (ramsey : BikovLocal.Ramsey C)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H C → BikovLocal.Sym H →
      ∀ a b, C a b → ¬H a b → ¬BikovLocal.Ramsey H)
    (w : V) (hw : (neighbors C w).Nonempty) :
    MarkedRel (fun a b : ↥(neighbors C w) => G a.val b.val) := by
  classical
  let S := neighbors C w
  let B : V→V→Prop := fun a b=>a≠w ∧ b≠w ∧ C a b
  have Bsub : BikovLocal.Sub B C := fun {_ _} h=>h.2.2
  have Bsym : BikovLocal.Sym B := fun {_ _} h=>⟨h.2.1,h.1,sym h.2.2⟩
  obtain ⟨v,hv⟩ := hw
  have Cwv : C w v := (mem_neighbors C).mp hv
  obtain ⟨old,cs,ok⟩ := not_ramsey_colors B
    (minimal B Bsub Bsym w v Cwv (fun h=>h.1 rfl))
  refine ⟨fun a b => old a.val b.val,fun a b => cs _ _,?_⟩
  rintro ⟨f,okf⟩
  let g (x : V) := if hx : x∈S then f ⟨x,hx⟩ else false
  have linked (a b : V) (wa : C w a) (wb : C w b) (ab : C a b) :
      ¬ (g a=old a b ∧ g b=old a b) := by
    have am : a∈S := (mem_neighbors C).mpr wa
    have bm : b∈S := (mem_neighbors C).mpr wb
    have q := okf ⟨a,am⟩ ⟨b,bm⟩ (sub ab)
    simpa [g,am,bm] using q
  obtain ⟨cc,css,good,_⟩ := BikovLocal.lift_link C (fun {_ _} h=>sym h) irr w old cs ok g linked
  exact ramsey cc css good

#print axioms ambient_core_link_marked
end Erdos151H13
