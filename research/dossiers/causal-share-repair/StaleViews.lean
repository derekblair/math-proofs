import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Equiv.Basic

namespace StaleViews

variable {F A B C : Type*} [AddGroup F]

/-- A pair of consecutive share values carries exactly the earlier value
and the additive increment, with no extra restriction on the field. -/
def pairDelta : (F × F) ≃ (F × F) where
  toFun p := (p.1,p.2-p.1)
  invFun p := (p.1,p.2+p.1)
  left_inv := by intro p; rcases p with ⟨a,b⟩; simp
  right_inv := by intro p; rcases p with ⟨a,b⟩; simp

def raw (u : A → F) (v w : B → F) (x y : C → F) :=
  (u, (fun i => (v i, w i)), (fun j => (x j, y j)))

def normal (u : A → F) (v w : B → F) (x y : C → F) :=
  (u, (fun i => (v i, w i-v i)), (fun j => (x j, y j-x j)))

theorem transcript_equiv
    (u u' : A → F) (v w v' w' : B → F) (x y x' y' : C → F) :
    raw u v w x y = raw u' v' w' x' y' ↔ normal u v w x y = normal u' v' w' x' y' := by
  let T := Equiv.prodCongr (Equiv.refl (A → F))
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.refl B) (pairDelta (F:=F)))
      (Equiv.arrowCongr (Equiv.refl C) (pairDelta (F:=F))))
  exact T.injective.eq_iff.symm

#print axioms pairDelta
#print axioms transcript_equiv
end StaleViews
