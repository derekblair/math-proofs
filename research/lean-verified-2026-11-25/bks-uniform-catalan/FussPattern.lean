import Pack
import Mathlib.Data.Fintype.EquivFin

namespace FussCover

def width (z p h : ℕ) : ℕ := 2*z+h+p+3
def step (z p h : ℕ) : ℕ := z+h+p+1

/-- z is the number of forced shared head positions, p the Fuss parameter,
and h the number of extra private head positions. Actual overlap is z+2. -/
def rank (z p h i : ℕ) : ℕ :=
  let F := 2*z+h
  if i<z then i
  else if i=z then F+1
  else if i=z+1 then F+p+2
  else if i<z+2+h then i-2
  else if i<step z p h then F+3+(i-(z+2+h))
  else if i<step z p h+z then z+h+(i-step z p h)
  else if i=step z p h+z then F
  else F+2

lemma rank_lt {z p h i : ℕ} (hp : 0<p) (hi : i<width z p h) :
    rank z p h i<width z p h := by
  unfold rank width step at *
  dsimp only
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
lemma rank_inj {z p h i j : ℕ} (hp : 0<p)
    (hi : i<width z p h) (hj : j<width z p h)
    (he : rank z p h i=rank z p h j) : i=j := by
  unfold rank width step at *
  dsimp only at he
  split_ifs at he <;> omega

noncomputable def pattern (z p h : ℕ) (hp : 0<p) : Equiv.Perm (Fin (width z p h)) :=
  Equiv.ofBijective (fun i => ⟨rank z p h i.val,rank_lt hp i.isLt⟩)
    ((Finite.injective_iff_bijective).mp
      (fun i j e => Fin.ext (rank_inj hp i.isLt j.isLt (congrArg Fin.val e))))

end FussCover
