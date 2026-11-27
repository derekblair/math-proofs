import TightLift

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V]

def restrictBool {W : Type*} (inside : W → Bool) (p : In inside → Bool) (w : W) : Bool :=
  if h : inside w=true then p ⟨w,h⟩ else false

def inLabel (B : V → Bool) (u : V) : Option (In B) → V
  | none => u
  | some v => v.val

theorem inLabel_injective (B : V → Bool) (u : V) (out : B u=false) :
    Function.Injective (inLabel B u) := by
  intro a b e
  cases a <;> cases b
  · rfl
  · rename_i v
    have ne : u≠v.val := fun h => by have H := v.property; rw [←h,out] at H; contradiction
    exact False.elim (ne e)
  · rename_i v
    have ne : v.val≠u := fun h => by have H := v.property; rw [h,out] at H; contradiction
    exact False.elim (ne e)
  · exact congrArg some (Subtype.ext e)

/-- A tight cut of the quotient, taking the side away from the contraction
vertex, is also tight in the original graph, with the same inside vertices. -/
theorem quotient_cut_lifts (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (inward : Inward I A B) (tight : Tight I A B)
    (a : In A → Bool) (b : Option (In B) → Bool) (port_out : b none=false)
    (small : Tight (pointsContraction I A B) a b) :
    Tight I (restrictBool A a) (restrictBool B (b ∘ some)) := by
  intro m hm
  obtain ⟨u,cu,uniq⟩ := tight m hm
  have out : B u=false := by
    cases hp : B u
    · rfl
    · exact False.elim (cu ((inward _ _ (hm u) hp).trans hp.symm))
  have port : A (m u)=true := by
    cases hp : A (m u)
    · exact False.elim (cu (hp.trans out.symm))
    · rfl
  let fn := projected A B m u (fun w hw => inward _ _ (hm w) hw) port
  let q := Equiv.ofBijective fn (projected_bijective A B m u out _ port uniq)
  have Q : ∀ z, pointsContraction I A B (q z) z := by
    intro z
    cases z with
    | none => exact ⟨u,out,hm u⟩
    | some v => exact hm v.val
  let cross (v : V) := restrictBool A a (m v) ≠ restrictBool B (b ∘ some) v
  have p (z : Option (In B)) : cross (inLabel B u z) ↔ a (q z)≠b z := by
    cases z with
    | none => simp [cross,inLabel,restrictBool,out,port,port_out,fn,q,projected]
    | some v =>
      have av : A (m v.val)=true := inward _ _ (hm v.val) v.property
      simp [cross,inLabel,restrictBool,v.property,av,fn,q,projected]
  have hit (v : V) (hc : cross v) : ∃ z, inLabel B u z=v := by
    by_cases yes : B v=true
    · exact ⟨some ⟨v,yes⟩,rfl⟩
    · have yes' : B v=false := by cases ee : B v <;> simp_all
      have ltrue : A (m v)=true := by
        by_contra no
        exact hc (by simp [restrictBool,no,yes])
      exact ⟨none,(uniq _ (by simp [ltrue,yes'])).symm⟩
  obtain ⟨z,hz,zz⟩ := small q Q
  refine ⟨inLabel B u z,(p z).mpr hz,?_⟩
  intro v hv
  obtain ⟨w,e⟩ := hit v hv
  have hw : a (q w)≠b w := (p w).mp (e.symm ▸ hv)
  exact e.symm.trans (congrArg (inLabel B u) (zz w hw))

#print axioms quotient_cut_lifts
end FolkmanB4.Tight
