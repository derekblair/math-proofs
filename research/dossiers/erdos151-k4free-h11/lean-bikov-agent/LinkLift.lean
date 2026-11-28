import Mathlib.Data.Set.Insert

namespace BikovLocal

variable {V : Type*}

def Safe (adj : V→V→Prop) (col : V→V→Bool) : Prop :=
  ∀ a b c, adj a b → adj b c → adj c a →
    ¬ (col a b=col b c ∧ col b c=col c a)

/-- Edges in a single link are exactly the extension constraints. This version
uses a total symmetric edge-coloring so no lifting/quotient conventions on
unordered pairs affect the ambient result. -/
theorem lift_link (adj : V→V→Prop) (sym : ∀ ⦃a b⦄, adj a b → adj b a) (irr : ∀ a, ¬ adj a a)
    (v : V) (col : V→V→Bool) (csym : ∀ a b, col a b=col b a)
    (old : Safe (fun a b => a≠v ∧ b≠v ∧ adj a b) col)
    (f : V→Bool)
    (linked : ∀ a b, adj v a → adj v b → adj a b →
      ¬ (f a=col a b ∧ f b=col a b)) :
    ∃ C : V→V→Bool, (∀ a b,C a b=C b a) ∧ Safe adj C ∧
      (∀ a b,a≠v → b≠v → C a b=col a b) := by
  classical
  let C (a b : V) := if a=v then f b else if b=v then f a else col a b
  have Csym (a b) : C a b=C b a := by
    by_cases x : a=v <;> by_cases y : b=v
    · simp [C,x,y]
    · simp [C,x,y]
    · simp [C,x,y]
    · exact (by simpa [C,x,y] using csym a b)
  have one (a b : V) (x : adj v a) (y : adj a b) (z : adj b v) :
      ¬ (C v a=C a b ∧ C a b=C b v) := by
    have na : a≠v := fun eq=>irr v (eq ▸ x)
    have nb : b≠v := fun eq=>irr v (eq ▸ z)
    intro h
    have l : f a=col a b := by simpa [C,na,nb] using h.1
    have r : col a b=f b := by simpa [C,na,nb] using h.2
    exact linked a b x (sym z) y ⟨l,r.symm⟩
  refine ⟨C,Csym,?_,fun a b na nb=>by simp [C,na,nb]⟩
  intro a b c ab bc ca he
  by_cases ha : a=v
  · subst a
    exact one b c ab bc ca he
  by_cases hb : b=v
  · subst b
    exact one c a bc ca ab ⟨he.2,he.2.symm.trans he.1.symm⟩
  by_cases hc : c=v
  · subst c
    exact one a b ca ab bc ⟨he.2.symm.trans he.1.symm,he.1⟩
  apply old a b c ⟨ha,hb,ab⟩ ⟨hb,hc,bc⟩ ⟨hc,ha,ca⟩
  simpa [C,ha,hb,hc] using he

#print axioms lift_link
end BikovLocal
