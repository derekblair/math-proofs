import BraceSquares
import TightSigning
import FanoLinePort

namespace FolkmanB4.Tight
open Critical
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

theorem no_disjoint_quotient_squares (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (covered : Covered I) (tight : Tight I A B) (k : V ≃ L)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm))
    [DecidableRel (pointsContraction I A B)]
    (H : NoSmallCut (pointsContraction I A B))
    (M : ∃ m : Option (In B) ≃ In A, ∀ v, pointsContraction I A B (m v) v)
    (deg : lns (pointsContraction I A B) none≤3) :
    ¬ ∃ s t : Square (pointsContraction I A B), Disjoint s.edges t.edges := by
  rintro ⟨s,t,disj⟩
  have impossible (w : Square (pointsContraction I A B))
      (p : w.v₁≠none) (q : w.v₂≠none) : False := by
    obtain ⟨x,xx⟩ : ∃ x : In B, w.v₁=some x := by
      cases h : w.v₁
      · exact False.elim (p h)
      · exact ⟨_,rfl⟩
    obtain ⟨y,yy⟩ : ∃ y : In B, w.v₂=some y := by
      cases h : w.v₂
      · exact False.elim (q h)
      · exact ⟨_,rfl⟩
    obtain ⟨m,hm,ha,hb⟩ := w.central H M
    rw [xx,yy] at ha hb
    have ne : x≠y := by
      intro e
      exact w.vne (xx.trans ((congrArg some e).trans yy.symm))
    exact no_central_square_off_port I A B covered tight k signs m hm ne ha hb
  rcases s.off_column_of_disjoint t disj none deg with h|h
  · exact impossible s h.1 h.2
  · exact impossible t h.1 h.2

theorem same_sign_transpose (I : L → V → Prop) (k : V ≃ L)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm))
    (s t : L ≃ V) (S : ∀ i, I i (s i)) (T : ∀ i, I i (t i)) :
    pSign (s.trans k)=pSign (t.trans k) := by
  have hs (i : V) : I (s.symm i) i := by simpa using S (s.symm i)
  have ht (i : V) : I (t.symm i) i := by simpa using T (t.symm i)
  have mid := signs s.symm t.symm hs ht
  have loop (u : L ≃ V) : pSign (u.trans k)=pSign (u.symm.trans k.symm) := by
    unfold pSign
    congr 2
    have e : k.permCongr (u.symm.trans k.symm) = (u.trans k : Equiv.Perm L)⁻¹ := by
      ext l
      simp [Equiv.permCongr_apply]
    have he := congrArg Equiv.Perm.sign e
    rw [Equiv.Perm.sign_permCongr,Equiv.Perm.sign_inv] at he
    exact he.symm
  exact (loop s).trans (mid.trans (loop t).symm)

#print axioms no_disjoint_quotient_squares
#print axioms same_sign_transpose
end FolkmanB4.Tight

namespace FolkmanB4.Fano
def dual : Equiv.Perm (Fin 7) :=
  ⟨![3,1,5,0,4,2,6],![3,1,5,0,4,2,6],by decide,by decide⟩

theorem self_dual : ∀ l p : Fin 7, inc (dual p) (dual l) ↔ inc l p := by decide

#print axioms self_dual
end FolkmanB4.Fano
