import RibbonAllOddSurface
import RibbonAllOddBase
import RibbonAllOddSlopeFinalCore
import RibbonAllOddResidual

namespace RibbonAllOddField
open RibbonStationaryField (Fault branch branches base chooseCase base_valid)
open RibbonAffine (pl)
variable {K : Type*} [Field K]

def oldTo (k : RibbonStationaryWord.Count) : Count := Fin.castLE (by decide) k

private theorem old_spec (k : RibbonStationaryWord.Count) : spec (oldTo k)=RibbonStationaryWord.spec k := by
  fin_cases k <;> rfl

private theorem lift_sep (a b : Kˣ) (k : RibbonStationaryWord.Count)
    (S : RibbonStationaryField.separates a b k) : separates a b (oldTo k) := by
  intro i j l E
  have H := S i j l (by simpa only [symbol,old_spec,RibbonStationaryField.symbol] using E)
  unfold IsMate
  rw [old_spec]
  exact H

private theorem drop_sep (a b : Kˣ) (k : RibbonStationaryWord.Count)
    (S : separates a b (oldTo k)) : RibbonStationaryField.separates a b k := by
  intro i j l E
  have H := S i j l (by simpa only [symbol,old_spec,RibbonStationaryField.symbol] using E)
  unfold IsMate at H
  rw [old_spec] at H
  exact H

private theorem surface_residual (a b : Kˣ) (P : RibbonStationaryField.SurfaceResidual a b) :
    FieldResidual a b := by
  obtain ⟨p,A,B⟩ := P
  rcases B with B|B|B|B|B
  · exact ⟨11,5,1,p,A,by simpa using B,by decide⟩
  · exact ⟨11,5,3,p,A,B,by decide⟩
  · exact ⟨11,5,4,p,A,B,by decide⟩
  · exact ⟨11,5,5,p,A,B,by decide⟩
  · exact ⟨11,5,9,p,A,B,by decide⟩

def SlopeWords : Prop :=
  ∀ (r : Fin 76) (t : Kˣ) (n : Nat), (2:K)≠0 → Odd n → t^n=1 → t≠1 →
    pl t 1 (branch r.val).p=0 →
    (∃ k : Count, separates (t^(branch r.val).v) (t^(-(branch r.val).u)) k) ∨
      ResidueRoot (branch r.val) t

theorem field_words_of (slope_full : SlopeWords (K:=K)) (a b : Kˣ) (n : Nat) (two : (2:K)≠0) (odd : Odd n)
    (aN : a^n=1) (bN : b^n=1) (a1 : a≠1) :
    (∃ k : Count, separates a b k) ∨ FieldResidual a b := by
  classical
  by_cases S : RibbonStationaryField.separates a b base
  · exact Or.inl ⟨oldTo base,lift_sep a b _ S⟩
  have F : Fault branch a b n := by
    unfold RibbonStationaryField.separates at S
    push_neg at S
    obtain ⟨i,j,l,E,ne⟩ := S
    exact (failure_for_odd branch base i j (chooseCase i j) (base_valid i j l) (odd_case_valid i j)
      a b n aN bN a1 odd two E).resolve_left ne
  rcases F with h|⟨r,t,aT,bT,tn,t1,p⟩
  · exact (surface_odd a b n h two odd aN bN a1).imp
      (fun ⟨k,S⟩ => ⟨oldTo k,lift_sep a b k S⟩) (surface_residual a b)
  · have rlt : r<76 := by
      by_contra! h
      have L : branches.size=76 := by decide +kernel
      have H : ¬r<branches.size := by omega
      have V : (branch r).v=0 := by simp [branch,getElem!_neg branches r H]; rfl
      exact a1 (by simpa [V] using aT)
    rcases slope_full ⟨r,rlt⟩ t n two odd tn t1 p with S|R
    · rw [aT,bT]
      exact Or.inl S
    · exact Or.inr (residual_from_root (branch r) t a b aT bT a1 R)

end RibbonAllOddField
#print axioms RibbonAllOddField.field_words_of
