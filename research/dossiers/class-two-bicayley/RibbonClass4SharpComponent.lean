import RibbonClass4Sharp

namespace RibbonClass4SharpGraph

abbrev Reach := Relation.ReflTransGen (Ribbon.Adj a b)
abbrev Root : V := (false,1)
abbrev Component := {u : V // Reach Root u}
def AdjComponent (u v : Component) : Prop := Ribbon.Adj a b u.val v.val

theorem connected_component (u v : Component) : Relation.ReflTransGen AdjComponent u v := by
  let r : Component := ⟨Root,.refl⟩
  have right (u' : Component) : Relation.ReflTransGen AdjComponent r u' := by
    obtain ⟨x,hx⟩ := u'
    induction hx with
    | refl => exact .refl
    | tail _ E ih => exact ih.tail E
  have left (u' : Component) : Relation.ReflTransGen AdjComponent u' r := by
    have H := right u'
    induction H with
    | refl => exact .refl
    | tail _ E ih => exact ih.head (symm E)
  exact (left u).trans (right v)

private theorem move_adj (g : H) {u v : V} (E : Ribbon.Adj a b u v) :
    Ribbon.Adj a b (left g u) (left g v) := by
  rcases E with ⟨hu,hv,h|h⟩|⟨hu,hv,h|h⟩|⟨h,k⟩
  · exact Or.inl ⟨hu,hv,Or.inl (by simpa [left,mul_assoc] using congrArg (g*·) h)⟩
  · exact Or.inl ⟨hu,hv,Or.inr (by simpa [left,mul_assoc] using congrArg (g*·) h)⟩
  · exact Or.inr (Or.inl ⟨hu,hv,Or.inl (by simpa [left,mul_assoc] using congrArg (g*·) h)⟩)
  · exact Or.inr (Or.inl ⟨hu,hv,Or.inr (by simpa [left,mul_assoc] using congrArg (g*·) h)⟩)
  · exact Or.inr (Or.inr ⟨h,congrArg (g*·) k⟩)

private theorem each_origin (s : Bool) : Reach Root (s,1) := by
  cases s
  · exact .refl
  · exact .single (Or.inr (Or.inr ⟨by decide,rfl⟩))

def ComponentCycle (n : Nat) : Prop :=
  ∃ f : Fin n → Component, Function.Injective f ∧
    ∀ i, AdjComponent (f i) (f ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem spectra (n : Nat) (hn : 0<n) : ComponentCycle n ↔ Ribbon.Cycle a b n := by
  constructor
  · rintro ⟨f,fi,fa⟩
    exact ⟨Subtype.val ∘ f,fun _ _ e => fi (Subtype.ext e),fa⟩
  · rintro ⟨f,fi,fa⟩
    let z : Fin n := ⟨0,hn⟩
    let g := (f z).2⁻¹
    let w := left g ∘ f
    have origin : Reach Root (w z) := by
      have E : w z = ((f z).1,1) := by simp [w,left,g]
      rw [E]
      exact each_origin _
    have edges (i : Fin n) : Ribbon.Adj a b (w i) (w ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩) :=
      move_adj g (fa i)
    have reach (i : Nat) (hi : i<n) : Reach Root (w ⟨i,hi⟩) := by
      induction i with
      | zero => exact origin
      | succ i ih =>
        have E : (⟨(i+1)%n,Nat.mod_lt _ hn⟩ : Fin n)=⟨i+1,hi⟩ :=
          Fin.ext (Nat.mod_eq_of_lt hi)
        have W := edges ⟨i,by omega⟩
        rw [E] at W
        exact (ih (by omega)).tail W
    exact ⟨fun i => ⟨w i,reach i.val i.isLt⟩,
      fun _ _ h => fi (left_inj g (congrArg Subtype.val h)), edges⟩

theorem connected_sharp :
    ¬ComponentCycle 4 ∧ ¬ComponentCycle 8 ∧ ¬ComponentCycle 16 ∧ ComponentCycle 32 := by
  exact ⟨fun h => sharp.1 ((spectra 4 (by decide)).mp h),
    fun h => sharp.2.1 ((spectra 8 (by decide)).mp h),
    fun h => sharp.2.2.1 ((spectra 16 (by decide)).mp h),
    (spectra 32 (by decide)).mpr sharp.2.2.2⟩

end RibbonClass4SharpGraph
#print axioms RibbonClass4SharpGraph.connected_component
#print axioms RibbonClass4SharpGraph.connected_sharp
