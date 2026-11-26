import RibbonStationarySurface
import RibbonStationarySlopeFinalCore

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (pl)
variable {K : Type*} [Field K]

def SlopeWords : Prop :=
  ∀ (r : Fin 76) (t : Kˣ) (n : Nat), (2:K)≠0 → Odd n → (¬3∣n) → t^n=1 → t≠1 →
    pl t 1 (branch r.val).p=0 →
    (∃ k : Count, separates (t^(branch r.val).v) (t^(-(branch r.val).u)) k) ∨
      ((11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9))

theorem field_words_of (slope_full : SlopeWords (K:=K)) (a b : Kˣ) (n : Nat) (two : (2:K)≠0) (odd : Odd n) (no3 : ¬3∣n)
    (aN : a^n=1) (bN : b^n=1) (a1 : a≠1) :
    (∃ k : Count, separates a b k) ∨ FieldResidual a b := by
  classical
  by_cases S : separates a b base
  · exact Or.inl ⟨base,S⟩
  have F : Fault branch a b n := by
    unfold separates at S
    push_neg at S
    obtain ⟨i,j,l,E,ne⟩ := S
    exact (failure branch base i j (chooseCase i j) (base_valid i j l)
      a b n aN bN a1 odd no3 two E).resolve_left ne
  rcases F with h|⟨r,t,aT,bT,tn,t1,p⟩
  · exact (surface_full a b n h two odd no3 aN bN a1).imp_right fun ⟨P,A,B⟩ =>
      ⟨P,fun eq => a1 (Units.ext eq),Or.inr (Or.inr (Or.inl A)),B⟩
  · have rlt : r<76 := by
      by_contra! h
      have L : branches.size=76 := by decide +kernel
      have H : ¬r<branches.size := by omega
      have V : (branch r).v=0 := by simp [branch,getElem!_neg branches r H]; rfl
      exact a1 (by simpa [V] using aT)
    rcases slope_full ⟨r,rlt⟩ t n two odd no3 tn t1 p with S|R
    · rw [aT,bT]
      exact Or.inl S
    · exact Or.inr (residual_from_t t a b (branch r).u (branch r).v aT bT a1 R)

end RibbonStationaryField
#print axioms RibbonStationaryField.field_words_of
