import RibbonD3FieldCompleteCore
import RibbonD3FieldSlope
import RibbonD3FieldDirect

namespace RibbonD3Field
open RibbonAffine (pl)
open RibbonStationaryField (Branch)
variable {K : Type*} [Field K]

private theorem outside_bad_bounds (p x y : Nat) (H : (p,x,y)∈exactBad) :
    (p=11 ∨ p=23 ∨ p=29) ∧ x<p ∧ y<p := by
  have X : (exactBad.all fun r => decide ((r.1=11 ∨ r.1=23 ∨ r.1=29) ∧
      r.2.1<r.1 ∧ r.2.2<r.1))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp X _ H)

private theorem outside_bad_flip (p x y : Nat) (H : (p,x,y)∈exactBad) : (p,y,x)∈exactBad := by
  have X : (exactBad.all fun r => decide ((r.1,r.2.2,r.2.1)∈exactBad))=true :=
    by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp X _ H)

/-- Field-only classification. It neither asserts group word closure nor
assumes that equality in an affine chart lifts to group equality. -/
theorem field_outside_surfaces (a b : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n)
    (two : (2:K)≠0) (three : (3:K)≠0) (an : a^n=1) (bn : b^n=1) (a1 : a≠1)
    (avoid : ∀ c : Int, surfaceIndex c → pl a b (surfacePoly c) ≠ 0) :
    (∃ k : Count, Separates (chart k) a b) ∨
      ∃ (p : Nat), (p=11 ∨ p=23 ∨ p=29) ∧
        ∃ (f : ZMod p→+*K) (x y : ZMod p),
          f x=(a:K) ∧ f y=(b:K) ∧ (p,x.val,y.val)∈exactBad := by
  have A : (∃ k, Ordered (chart k) a b) ∨ ScalarPair a b := by
    rcases base_cases a b n an bn a1 odd no3 two three with h|⟨c,C,H⟩|⟨j,t,aT,bT,tn,t1,P⟩
    · exact Or.inl ⟨0,h⟩
    · exact False.elim (avoid c C H)
    · have jlt : j<88 := by
        by_contra! h
        have L : branches.size=88 := by decide +kernel
        have H : ¬j<branches.size := by omega
        have V : (branch j).v=0 := by simp [branch,getElem!_neg branches j H]; rfl
        exact a1 (by simpa [V] using aT)
      have tt : t^(branch j).v≠1 := fun h => a1 (aT.trans h)
      rw [aT,bT]
      exact slope_cases ⟨j,jlt⟩ t n odd no3 tn t1 tt two three P

  rcases A with ⟨k,S⟩ | E
  · exact Or.inl ⟨k,separate (chart k) (charts_shape k) a b S⟩
  rcases scalar_cases a b E with ⟨k,S⟩ | ⟨p,x,y,hp,P,A,B,h⟩
  · exact Or.inl ⟨k,separate (chart k) (charts_shape k) a b S⟩
  obtain ⟨pb,hx,hy⟩ := outside_bad_bounds p x y h
  obtain ⟨f,u,v,U,V,X,Y⟩ := scalar_digit p hp a b x y P A B hx hy
  exact Or.inr ⟨p,pb,f,u,v,U,V,by rwa [X,Y]⟩

end RibbonD3Field
#print axioms RibbonD3Field.field_outside_surfaces
