import HeadCoords
import Mathlib.Logic.Equiv.Fin.Basic

namespace FussCover

abbrev Labels (z h j : ℕ) := Fin (hN z h j) ⊕ (Fin (j+1) ⊕ Fin (j+1))

def toPos {z h j : ℕ} (hj : 0<j) (hz : 0<z) : Labels z h j → Fin (n z h j)
  | .inl u => hAt hj hz u
  | .inr (.inl t) => A hj t
  | .inr (.inr t) => B hj t

lemma toPos_surj {z h j : ℕ} (hj : 0<j) (hz : 0<z) :
    Function.Surjective (toPos (z:=z) (h:=h) hj hz) := by
  intro v
  rcases vertex_cover hj v with ⟨t,i,E⟩|⟨t,i,E⟩|⟨t,E⟩|⟨t,E⟩
  · exact ⟨.inl (hLowID t i), (hAt_low hj hz t i).trans E.symm⟩
  · exact ⟨.inl (hPrvID t i), (hAt_private hj hz t i).trans E.symm⟩
  · exact ⟨.inr (.inl t), E.symm⟩
  · exact ⟨.inr (.inr t), E.symm⟩

def labCardEquiv {z h j : ℕ} (hj : 0<j) : Labels z h j ≃ Fin (n z h j) := by
  unfold Labels
  refine (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans (finSumFinEquiv.trans (finCongr ?_))
  rw [n_eq_head_core hj]
  omega

noncomputable def posEquiv {z h j : ℕ} (hj : 0<j) (hz : 0<z) :
    Labels z h j ≃ Fin (n z h j) := by
  let f := toPos (z:=z) (h:=h) hj hz
  let e := labCardEquiv (z:=z) (h:=h) hj
  have s : Function.Surjective f := toPos_surj hj hz
  refine Equiv.ofBijective f ⟨?_,s⟩
  have S : Function.Surjective (f ∘ e.symm) := s.comp e.symm.surjective
  have I := S.bijective_of_finite.1
  intro a b E
  have eb : (f ∘ e.symm) (e a) = (f ∘ e.symm) (e b) := by simpa [Function.comp_def] using E
  exact e.injective (I eb)

@[simp] lemma posEquiv_apply {z h j : ℕ} (hj : 0<j) (hz : 0<z) (a : Labels z h j) :
    posEquiv hj hz a = toPos hj hz a := rfl

end FussCover
