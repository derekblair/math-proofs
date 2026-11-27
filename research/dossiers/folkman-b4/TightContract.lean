import TightCard

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V]

abbrev In (A : L → Bool) := {l : L // A l = true}

/-- Label the contracted vertex by `none`. A cut directed from outside
columns to inside rows keeps every inside column and adds one new column. -/
def projected (A : L → Bool) (B : V → Bool) (m : V ≃ L) (u : V)
    (inward : ∀ v, B v=true → A (m v)=true) (atPort : A (m u)=true) :
    Option (In B) → In A
  | none => ⟨m u,atPort⟩
  | some v => ⟨m v.val,inward v.val v.property⟩

theorem projected_bijective (A : L → Bool) (B : V → Bool) (m : V ≃ L) (u : V)
    (out : B u=false) (inward : ∀ v, B v=true → A (m v)=true)
    (atPort : A (m u)=true) (unique : ∀ v, A (m v)≠B v → v=u) :
    Function.Bijective (projected A B m u inward atPort) := by
  constructor
  · intro x y H
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some v =>
        have h : u=v.val := m.injective (congrArg Subtype.val H)
        have q := v.property
        rw [←h,out] at q
        contradiction
    | some v =>
      cases y with
      | none =>
        have h : v.val=u := m.injective (congrArg Subtype.val H)
        have q := v.property
        rw [h,out] at q
        contradiction
      | some w =>
        exact congrArg some (Subtype.ext (m.injective (congrArg Subtype.val H)))
  · intro l
    let v := m.symm l.val
    have e : m v=l.val := m.apply_symm_apply l.val
    by_cases z : B v=true
    · exact ⟨some ⟨v,z⟩,Subtype.ext e⟩
    · have ne : A (m v)≠B v := by rw [e,l.property]; exact fun h => z h.symm
      have t := unique v ne
      exact ⟨none,Subtype.ext (by change m u=l.val; rw [←t]; exact e)⟩

theorem lift_quotient_matching (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (m : V ≃ L) (u : V) (out : B u=false)
    (matchOK : ∀ v, I (m v) v)
    (atPort : A (m u)=true)
    (unique : ∀ v, A (m v)≠B v → v=u)
    (q : Option (In B) ≃ In A)
    (qp : (q none).val=m u)
    (qi : ∀ v : In B, I (q (some v)).val v.val) :
    ∃ n : V ≃ L, (∀ v, I (n v) v) ∧
      (∀ v : In B, n v.val=(q (some v)).val) ∧
      (∀ v, B v=false → n v=m v) := by
  classical
  let f (v : V) : L := if h : B v=true then (q (some ⟨v,h⟩)).val else m v
  have combine (v w : V) (hv : B v=true) (hw : B w≠true) (H : f v=f w) : False := by
    have eq : (q (some ⟨v,hv⟩)).val=m w := by simpa [f,hv,hw] using H
    have Aw : A (m w)=true := eq ▸ (q (some ⟨v,hv⟩)).property
    have iden : w=u := unique w (by rw [Aw]; exact fun h => hw h.symm)
    have eq' : (q (some ⟨v,hv⟩)).val=(q none).val := by rw [eq,iden,qp]
    have bad : some (⟨v,hv⟩ : In B)=none := q.injective (Subtype.ext eq')
    contradiction
  have hf : Function.Injective f := by
    intro v w H
    by_cases v1 : B v=true <;> by_cases w1 : B w=true
    · have e : (q (some ⟨v,v1⟩)).val = (q (some ⟨w,w1⟩)).val := by
        simpa [f,v1,w1] using H
      have F := Option.some.inj (q.injective (Subtype.ext e))
      exact congrArg Subtype.val F
    · exact False.elim (combine v w v1 w1 H)
    · exact False.elim (combine w v w1 v1 H.symm)
    · apply m.injective
      simpa [f,v1,w1] using H
  let n := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf,Fintype.card_congr m⟩)
  refine ⟨n,?_,?_,?_⟩
  · intro v
    change I (f v) v
    by_cases h : B v=true
    · simpa [f,h] using qi ⟨v,h⟩
    · simpa [f,h] using matchOK v
  · intro v
    change f v.val=_
    simp [f,v.property]
  · intro v h
    change f v=_
    simp [f,h]

#print axioms projected_bijective
#print axioms lift_quotient_matching
end FolkmanB4.Tight
