import RibbonD3WideBase
import RibbonD3WideOutcome
import RibbonD3WideTriData

namespace RibbonD3Wide
open RibbonD3Field
open RibbonAffine (pl)
variable {K : Type*} [Field K]

def SlopeInputs : Prop :=
  ∀ (i : Fin 88) (t : Kˣ) (n : Nat), Odd n → t^n=1 → t≠1 →
    t^(branch i.val).v≠1 → (2:K)≠0 → (3:K)≠0 → pl t 1 (branch i.val).p=0 →
    (∃ k, Ordered (chart k) (t^(branch i.val).v) (t^(-(branch i.val).u))) ∨
      ScalarPair (t^(branch i.val).v) (t^(-(branch i.val).u))

theorem field_cases (S : SlopeInputs (K:=K)) (a b : Kˣ) (n : Nat)
    (odd : Odd n) (two : (2:K)≠0) (three : (3:K)≠0) (an : a^n=1) (bn : b^n=1) (a1 : a≠1) :
    (∃ k : Count, Ordered (chart k) a b) ∨ FieldBad a b ∨
      ∃ c : Int, surfaceIndex c ∧ pl a b (surfacePoly c)=0 := by
  rcases base_cases a b n an bn a1 odd two three with h|⟨c,C,H⟩|⟨j,t,aT,bT,tn,t1,P⟩
  · exact Or.inl ⟨0,h⟩
  · exact Or.inr (Or.inr ⟨c,C,H⟩)
  · have jlt : j<88 := by
      by_contra! h
      have L : branches.size=88 := by decide +kernel
      have H : ¬j<branches.size := by omega
      have V : (branch j).v=0 := by simp [branch,getElem!_neg branches j H]; rfl
      exact a1 (by simpa [V] using aT)
    have tt : t^(branch j).v≠1 := fun h => a1 (aT.trans h)
    rcases S ⟨j,jlt⟩ t n odd tn t1 tt two three P with ⟨k,C⟩|F
    · rw [←aT,←bT] at C
      exact Or.inl ⟨k,C⟩
    · rw [←aT,←bT] at F
      rcases scalar_cases a b F with Q|R
      · exact Or.inl Q
      · exact Or.inr (Or.inl R)

def InvertedSeparates (a b : Kˣ) : Prop :=
  ∃ (invertX invertY : Bool) (k : Count), (if invertX then a⁻¹ else a)≠1 ∧
    Separates (chart k) (if invertX then a⁻¹ else a) (if invertY then b⁻¹ else b)

/-- Slope certificates are the only callback; the base and all five surfaces
in all three tested orientations are already checked. -/
theorem inversion_cover_of_slopes (S : SlopeInputs (K:=K)) (a b : Kˣ) (n : Nat)
    (odd : Odd n) (two : (2:K)≠0) (three : (3:K)≠0)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1) :
    InvertedSeparates a b ∨ FieldBad a b := by
  rcases field_cases S a b n odd two three an bn a1 with ⟨k,M⟩|F|⟨c,C,H⟩
  · exact Or.inl ⟨false,false,k,a1,separate _ (charts_shape k) a b M⟩
  · exact Or.inr F
  have av : (a⁻¹)^n=1 := by rw [inv_pow,an,inv_one]
  have bv : (b⁻¹)^n=1 := by rw [inv_pow,bn,inv_one]
  have ai : a⁻¹≠1 := by simpa using a1
  rcases field_cases S a⁻¹ b n odd two three av bn ai with ⟨k,M⟩|F|⟨d,D,L⟩
  · exact Or.inl ⟨true,false,k,ai,separate _ (charts_shape k) a⁻¹ b M⟩
  · exact Or.inr (field_bad_inv_left a b F)
  rcases field_cases S a b⁻¹ n odd two three an bv a1 with ⟨k,M⟩|F|⟨e,E,M⟩
  · exact Or.inl ⟨false,true,k,a1,separate _ (charts_shape k) a b⁻¹ M⟩
  · exact Or.inr (field_bad_inv_right a b F)
  rcases scalar_cases a b (invert_surfaces_bad c d e C D E a b H L M a1 two three n odd an bn) with ⟨k,M⟩|F
  · exact Or.inl ⟨false,false,k,a1,separate _ (charts_shape k) a b M⟩
  · exact Or.inr F

end RibbonD3Wide
#print axioms RibbonD3Wide.inversion_cover_of_slopes
