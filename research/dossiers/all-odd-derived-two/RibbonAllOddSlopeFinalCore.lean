import RibbonAllOddModular
import RibbonAllOddExtras

namespace RibbonAllOddField
open RibbonStationaryField (Branch)
open RibbonAffine (pl)
variable {K : Type*} [Field K]

theorem slope_use (B : Branch) (C : Cover) (T : RowValid B.p C) (G : GeomValid B C)
    (p : ∀ k : Fin C.rows.size, ∃ r : PrimeCert, primeValid B C.rows[k] r)
    (t : Kˣ) (n : Nat) (two : (2:K)≠0) (odd : Odd n)
    (tn : t^n=1) (nt : t≠1) (F : pl t 1 B.p=0) :
    separates (t^B.v) (t^(-B.u)) C.k ∨
      ResidueRoot B t := by
  classical
  by_cases S : separates (t^B.v) (t^(-B.u)) C.k
  · exact Or.inl S
  right
  unfold separates at S
  push_neg at S
  obtain ⟨i,j,l,eq,h⟩ := S
  obtain ⟨r,H,M,N⟩ := (no_fallback_collision B C T G t n odd tn nt F i j l eq).resolve_left h
  obtain ⟨pc,V⟩ := p r
  exact prime_sound t n odd tn two B C.rows[r] pc V F H M N

end RibbonAllOddField
#print axioms RibbonAllOddField.slope_use
