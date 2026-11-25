import HeadOrder
import VertexEquiv

namespace FussCover

variable {z h j : ℕ} (hj : 0<j) (hz : 0<z)
variable (r : Equiv.Perm (Fin (n z h j))) (P : packed r)
include P

lemma packed_A_anti : StrictAnti (fun i : Fin (j+1) => r (A hj i)) := by
  let f : Fin (j+1) → (Fin (n z h j))ᵒᵈ := fun i => r (A hj i)
  exact (Fin.strictMono_iff_lt_succ (f:=f)).2 (fun i => local_A_desc hj r P i)

lemma packed_B_anti : StrictAnti (fun i : Fin (j+1) => r (B hj i)) := by
  let f : Fin (j+1) → (Fin (n z h j))ᵒᵈ := fun i => r (B hj i)
  exact (Fin.strictMono_iff_lt_succ (f:=f)).2 (fun i => local_B_desc hj r P i)

lemma packed_H_before_A (u : Fin (hN z h j)) (t : Fin (j+1)) :
    r (hAt hj hz u) < r (A hj t) := by
  let m : Fin z := ⟨z-1,by omega⟩
  let last : Fin (j+1) := ⟨j,by omega⟩
  let prev : Fin j := ⟨j-1,by omega⟩
  have e : prev.succ=last := Fin.ext (by change j-1+1=j; omega)
  have Hlast : r (hAt hj hz (hLowID last m)) < r (A hj last) := by
    rw [hAt_low]
    simpa only [e] using local_low_next_A hj r P prev m
  have uLe : u ≤ hLowID last m := by
    change u.val ≤ j*(z+h)+(z-1)
    have hu : u.val < j*(z+h)+z := u.isLt
    omega
  have tLe : t ≤ last := by
    change t.val ≤ j
    have := t.isLt
    omega
  exact ((packed_head_mono hj hz r P).monotone uLe).trans_lt
    (Hlast.trans_le ((packed_A_anti hj r P).antitone tLe))

lemma packed_Amin_before_B (t : Fin (j+1)) :
    r (A hj (Fin.last j)) < r (B hj t) := by
  let prev : Fin j := ⟨j-1,by omega⟩
  have e : prev.succ=Fin.last j := Fin.ext (by change j-1+1=j; omega)
  have q := (local_A_desc hj r P prev).trans (local_cross hj r P prev)
  rw [e] at q
  have tLe : t ≤ Fin.last j := Fin.le_last t
  exact q.trans_le ((packed_B_anti hj r P).antitone tLe)

lemma packed_A_before_Bmax (t : Fin (j+1)) :
    r (A hj t) < r (B hj 0) := by
  let first : Fin j := ⟨0,hj⟩
  have e : first.castSucc = (0 : Fin (j+1)) := Fin.ext rfl
  have q := (local_cross hj r P first).trans (local_B_desc hj r P first)
  rw [e] at q
  exact ((packed_A_anti hj r P).antitone (Fin.zero_le t)).trans_lt q

lemma packed_H_before_B (u : Fin (hN z h j)) (t : Fin (j+1)) :
    r (hAt hj hz u) < r (B hj t) :=
  (packed_H_before_A hj hz r P u (Fin.last j)).trans (packed_Amin_before_B hj r P t)

end FussCover
