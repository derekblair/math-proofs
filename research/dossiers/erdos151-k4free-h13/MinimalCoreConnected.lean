import CoreExtractMinimal
import Mathlib.Logic.Relation

namespace Erdős151.H12

variable {V : Type*}

theorem not_ramsey_colors (G : V → V → Prop) (h : ¬BikovLocal.Ramsey G) :
    ∃ c : V→V→Bool, (∀ a b,c a b=c b a) ∧ BikovLocal.Safe G c := by
  classical
  unfold BikovLocal.Ramsey at h
  push Not at h
  exact h

/-- Edge minimality makes the nonisolated host connected. -/
theorem minimal_core_reaches (G : V → V → Prop) (sym : BikovLocal.Sym G)
    (ramsey : BikovLocal.Ramsey G)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H G → BikovLocal.Sym H →
      ∀ a b, G a b → ¬H a b → ¬BikovLocal.Ramsey H)
    (w t : V) (wt : G w t) :
    ∀ u, (∃ v,G u v) → Relation.ReflTransGen G w u := by
  classical
  let P := Relation.ReflTransGen G w
  have own : P w := Relation.ReflTransGen.refl
  have prop {x y : V} (h : G x y) : P x ↔ P y :=
    ⟨fun h0 => h0.tail h,fun h0 => h0.tail (sym h)⟩
  intro u hu
  by_contra ou
  obtain ⟨v,uv⟩ := hu
  let A : V→V→Prop := fun a b => G a b ∧ P a ∧ P b
  let B : V→V→Prop := fun a b => G a b ∧ ¬P a ∧ ¬P b
  have sa : BikovLocal.Sym A := fun {_ _} h => ⟨sym h.1,h.2.2,h.2.1⟩
  have sb : BikovLocal.Sym B := fun {_ _} h => ⟨sym h.1,h.2.2,h.2.1⟩
  have subA : BikovLocal.Sub A G := fun {_ _} h => h.1
  have subB : BikovLocal.Sub B G := fun {_ _} h => h.1
  obtain ⟨ca,csa,oka⟩ := not_ramsey_colors A (minimal A subA sa u v uv (fun h => ou h.2.1))
  obtain ⟨cb,csb,okb⟩ := not_ramsey_colors B (minimal B subB sb w t wt (fun h => h.2.1 own))
  let c (a b : V) := if P a ∧ P b then ca a b else cb a b
  have cs (a b : V) : c a b=c b a := by simp [c,and_comm,csa a b,csb a b]
  apply ramsey c cs
  intro a b d ab bd da hc
  by_cases pa : P a
  · have pb := (prop ab).mp pa
    have pd := (prop bd).mp pb
    exact oka a b d ⟨ab,pa,pb⟩ ⟨bd,pb,pd⟩ ⟨da,pd,pa⟩ (by simpa [c,pa,pb,pd] using hc)
  · have pb : ¬P b := fun h => pa ((prop ab).mpr h)
    have pd : ¬P d := fun h => pb ((prop bd).mpr h)
    exact okb a b d ⟨ab,pa,pb⟩ ⟨bd,pb,pd⟩ ⟨da,pd,pa⟩ (by simpa [c,pa,pb,pd] using hc)

def CoreSupp (G : V→V→Prop) := {v : V // ∃ u,G v u}

def CoreAdj (G : V→V→Prop) (a b : CoreSupp G) : Prop := G a.val b.val

theorem core_path_support (G : V→V→Prop) {a b : V}
    (h : Relation.ReflTransGen G a b) (ha : ∃ u,G a u) (hb : ∃ u,G b u) :
    Relation.ReflTransGen (CoreAdj G) ⟨a,ha⟩ ⟨b,hb⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge ih =>
    exact (ih ⟨_,edge⟩).tail edge

theorem support_connected (G : V→V→Prop) (sym : BikovLocal.Sym G)
    (ramsey : BikovLocal.Ramsey G)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H G → BikovLocal.Sym H →
      ∀ a b, G a b → ¬H a b → ¬BikovLocal.Ramsey H) :
    ∀ a b : CoreSupp G, Relation.ReflTransGen (CoreAdj G) a b := by
  intro a b
  obtain ⟨t,wt⟩ := a.property
  have h := minimal_core_reaches G sym ramsey minimal a.val t wt b.val b.property
  exact core_path_support G h a.property b.property

theorem restrict_ramsey_to_support (G : V→V→Prop) (sym : BikovLocal.Sym G)
    (ramsey : BikovLocal.Ramsey G) : BikovLocal.Ramsey (CoreAdj G) := by
  classical
  intro c cs hc
  let f (a b : V) := if ha : ∃ x,G a x then
    if hb : ∃ x,G b x then c ⟨a,ha⟩ ⟨b,hb⟩ else false else false
  have fs (a b : V) : f a b=f b a := by
    by_cases h : ∃ x,G a x <;> by_cases k : ∃ x,G b x <;>
      simp [f,h,k] <;> exact cs _ _
  apply ramsey f fs
  intro a b d ab bd da hm
  have ah : ∃ x,G a x := ⟨b,ab⟩
  have bh : ∃ x,G b x := ⟨d,bd⟩
  have dh : ∃ x,G d x := ⟨a,da⟩
  exact hc ⟨a,ah⟩ ⟨b,bh⟩ ⟨d,dh⟩ ab bd da (by simpa [f,ah,bh,dh] using hm)

#print axioms minimal_core_reaches
#print axioms support_connected
#print axioms restrict_ramsey_to_support
end Erdős151.H12
