import RibbonD3FieldDirectCore
import RibbonD3FieldBase

namespace RibbonD3Field
open RibbonAffine (pl)
variable {K : Type*} [Field K]

def SlopeInputs : Prop :=
  ∀ (i : Fin 88) (t : Kˣ) (n : Nat), Odd n → (¬3∣n) → t^n=1 → t≠1 →
    t^(branch i.val).v≠1 → (2:K)≠0 → (3:K)≠0 → pl t 1 (branch i.val).p=0 →
    (∃ k, Ordered (chart k) (t^(branch i.val).v) (t^(-(branch i.val).u))) ∨
      ScalarPair (t^(branch i.val).v) (t^(-(branch i.val).u))

def SurfaceInputs : Prop :=
  ∀ (c : Int), surfaceIndex c → ∀ (a b : Kˣ) (n : Nat), Odd n → (¬3∣n) →
    (2:K)≠0 → (3:K)≠0 → a^n=1 → b^n=1 → a≠1 → pl a b (surfacePoly c)=0 →
    (∃ k, Ordered (chart k) a b) ∨ ScalarPair a b

theorem field_core (S : SlopeInputs (K:=K)) (F : SurfaceInputs (K:=K))
    (a b : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n)
    (two : (2:K)≠0) (three : (3:K)≠0) (an : a^n=1) (bn : b^n=1) (a1 : a≠1) :
    (∃ k, Ordered (chart k) a b) ∨ ScalarPair a b := by
  rcases base_cases a b n an bn a1 odd no3 two three with h|⟨c,C,H⟩|⟨j,t,aT,bT,tn,t1,P⟩
  · exact Or.inl ⟨0,h⟩
  · exact F c C a b n odd no3 two three an bn a1 H
  · have jlt : j<88 := by
      by_contra! h
      have L : branches.size=88 := by decide +kernel
      have H : ¬j<branches.size := by omega
      have V : (branch j).v=0 := by simp [branch,getElem!_neg branches j H]; rfl
      exact a1 (by simpa [V] using aT)
    have tt : t^(branch j).v≠1 := fun h => a1 (aT.trans h)
    rw [aT,bT]
    exact S ⟨j,jlt⟩ t n odd no3 tn t1 tt two three P

end RibbonD3Field
#print axioms RibbonD3Field.field_core
