import Geometry

namespace FussCover
open CoverCutoff

def asc {z h j : ℕ} (_hj : 0<j) (r : Equiv.Perm (Fin (n z h j))) :
    Fin (n z h j) → Fin (n z h j) → Prop := fun a b => r a < r b

def win {z h j : ℕ} (t : Fin j) (i : ℕ) (hi : i<wi z h) : Fin (n z h j) :=
  CoverCutoff.window t (⟨i,hi⟩ : Fin (wi z h))

lemma win_prefix {z h j : ℕ} (hj : 0<j) (t : Fin j) (i : ℕ) (hi : i<z+2) :
    win (z:=z) (h:=h) t i (by rw [wi_def]; omega) = pos hj t.castSucc i hi := rfl

lemma win_private {z h j : ℕ} (hj : 0<j) (t : Fin j) (i : Fin h) :
    win (z:=z) (h:=h) t (z+2+i.val) (by rw [wi_def,st_def];have := i.isLt;omega) =
      posP hj t i := rfl

lemma win_suffix {z h j : ℕ} (hj : 0<j) (t : Fin j) (i : ℕ) (hi : i<z+2) :
    win (z:=z) (h:=h) t (st z h+i) (by rw [wi_def];omega) = pos hj t.succ i hi := by
  apply Fin.ext
  change t.val*st z h+(st z h+i) = (t.val+1)*st z h+i
  rw [Nat.add_mul,one_mul,Nat.add_assoc]

lemma rank_prefix_low {z h i : ℕ} (hi : i<z) : rank z 1 h i=i := by simp [rank,hi]
lemma rank_prefix_A (z h : ℕ) : rank z 1 h z=2*z+h+1 := by simp [rank]
lemma rank_prefix_B (z h : ℕ) : rank z 1 h (z+1)=2*z+h+3 := by
  have h₁ : ¬z+1<z := by omega

  simp [rank,h₁]
lemma rank_private {z h : ℕ} (i : Fin h) : rank z 1 h (z+2+i.val)=z+i.val := by
  unfold rank
  dsimp only
  have := i.isLt
  split_ifs <;> omega
lemma rank_suffix_low {z h : ℕ} (i : Fin z) :
    rank z 1 h (st z h+i.val)=z+h+i.val := by
  change rank z 1 h (step z 1 h+i.val)=_
  unfold rank step
  dsimp only
  have := i.isLt
  split_ifs <;> omega
lemma rank_suffix_A (z h : ℕ) : rank z 1 h (st z h+z)=2*z+h := by
  change rank z 1 h (step z 1 h+z) = _
  unfold rank step
  dsimp only
  split_ifs <;> omega
lemma rank_suffix_B (z h : ℕ) : rank z 1 h (st z h+z+1)=2*z+h+2 := by
  change rank z 1 h (step z 1 h+z+1) = _
  unfold rank step
  dsimp only
  split_ifs <;> omega

end FussCover
