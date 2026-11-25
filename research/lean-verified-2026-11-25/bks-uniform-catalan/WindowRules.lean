import HeadCoords
namespace FussCover
open CoverCutoff

variable {z h j : ℕ} (hj : 0<j)
variable (r : Equiv.Perm (Fin (n z h j)))

def packed : Prop := Packs (pattern z 1 h (by decide)) (st z h) j r

lemma local_compare (P : packed r) (t : Fin j) (i l : ℕ) (hi : i<wi z h) (hl : l<wi z h) :
    r (win t i hi) < r (win t l hl) ↔ rank z 1 h i < rank z 1 h l :=
  P t ⟨i,hi⟩ ⟨l,hl⟩

lemma local_low_lt (P : packed r) (t : Fin j) {a b : Fin z} (lt : a < b) :
    r (headS hj t.castSucc a) < r (headS hj t.castSucc b) := by
  have t1 := local_compare r P t a.val b.val
    (by rw [wi_def]; have := a.isLt; omega) (by rw [wi_def]; have := b.isLt; omega)
  rw [win_prefix hj t a.val (by have := a.isLt; omega),
      win_prefix hj t b.val (by have := b.isLt; omega),
      rank_prefix_low a.isLt,rank_prefix_low b.isLt] at t1
  exact t1.mpr lt

lemma local_suffix_low_lt (P : packed r) (t : Fin j) {a b : Fin z} (lt : a < b) :
    r (headS hj t.succ a) < r (headS hj t.succ b) := by
  have t1 := local_compare r P t (st z h+a.val) (st z h+b.val)
    (by rw [wi_def];have := a.isLt;omega) (by rw [wi_def]; have := b.isLt;omega)
  rw [win_suffix hj t a.val (by have := a.isLt; omega),
      win_suffix hj t b.val (by have := b.isLt; omega),
      rank_suffix_low a,rank_suffix_low b] at t1
  have hlt : a.val<b.val := lt
  exact t1.mpr (by omega)

lemma local_pvt_lt (P : packed r) (t : Fin j) {a b : Fin h} (lt : a < b) :
    r (posP hj t a) < r (posP hj t b) := by
  have t1 := local_compare r P t (z+2+a.val) (z+2+b.val)
    (by rw [wi_def,st_def]; have := a.isLt; omega) (by rw [wi_def,st_def]; have := b.isLt; omega)
  rw [win_private hj t a,win_private hj t b,rank_private a,rank_private b] at t1
  have hlt : a.val<b.val := lt
  exact t1.mpr (by omega)

lemma local_low_pvt (P : packed r) (t : Fin j) (a : Fin z) (b : Fin h) :
    r (headS hj t.castSucc a) < r (posP hj t b) := by
  have t1 := local_compare r P t a.val (z+2 + b.val)
    (by rw [wi_def]; have := a.isLt; omega) (by rw [wi_def,st_def]; have := b.isLt; omega)
  rw [win_prefix hj t a.val (by have := a.isLt; omega),win_private hj t b,
      rank_prefix_low a.isLt,rank_private b] at t1
  have e := a.isLt
  exact t1.mpr (by omega)

lemma local_pvt_next (P : packed r) (t : Fin j) (a : Fin h) (b : Fin z) :
    r (posP hj t a) < r (headS hj t.succ b) := by
  have t1 := local_compare r P t (z+2+a.val) (st z h+b.val)
    (by rw [wi_def,st_def]; have := a.isLt; omega) (by rw [wi_def]; have := b.isLt; omega)
  rw [win_private hj t a,win_suffix hj t b.val (by have := b.isLt; omega),
      rank_private a,rank_suffix_low b] at t1
  have e := a.isLt
  exact t1.mpr (by omega)

lemma local_low_next (P : packed r) (t : Fin j) (a b : Fin z) :
    r (headS hj t.castSucc a) < r (headS hj t.succ b) := by
  have t1 := local_compare r P t a.val (st z h+b.val)
    (by rw [wi_def]; have := a.isLt; omega) (by rw [wi_def]; have := b.isLt; omega)
  rw [win_prefix hj t a.val (by have := a.isLt; omega),
      win_suffix hj t b.val (by have := b.isLt; omega),rank_prefix_low a.isLt,rank_suffix_low b] at t1
  have e := a.isLt
  exact t1.mpr (by omega)

lemma local_low_next_A (P : packed r) (t : Fin j) (a : Fin z) :
    r (headS hj t.succ a) < r (A hj t.succ) := by
  have t1 := local_compare r P t (st z h+a.val) (st z h+z)
    (by rw [wi_def]; have := a.isLt; omega) (by rw [wi_def]; omega)
  rw [win_suffix hj t a.val (by have := a.isLt; omega),win_suffix hj t z (by omega),
      rank_suffix_low a,rank_suffix_A] at t1
  have e := a.isLt
  exact t1.mpr (by omega)

lemma local_A_desc (P : packed r) (t : Fin j) :
    r (A hj t.succ) < r (A hj t.castSucc) := by
  have t1 := local_compare r P t (st z h+z) z (by rw [wi_def]; omega) (by rw [wi_def]; omega)
  rw [win_suffix hj t z (by omega), win_prefix hj t z (by omega),rank_suffix_A,rank_prefix_A] at t1
  exact t1.mpr (by omega)

lemma local_B_desc (P : packed r) (t : Fin j) :
    r (B hj t.succ) < r (B hj t.castSucc) := by
  have t1 := local_compare r P t (st z h+(z+1)) (z+1) (by rw [wi_def]; omega) (by rw [wi_def]; omega)
  rw [win_suffix hj t (z+1) (by omega),win_prefix hj t (z+1) (by omega),rank_prefix_B] at t1
  have e : rank z 1 h (st z h+(z+1)) = 2*z+h+2 := by rw [←Nat.add_assoc,rank_suffix_B]
  rw [e] at t1
  exact t1.mpr (by omega)

lemma local_cross (P : packed r) (t : Fin j) :
    r (A hj t.castSucc) < r (B hj t.succ) := by
  have t1 := local_compare r P t z (st z h+(z+1)) (by rw [wi_def]; omega) (by rw [wi_def]; omega)
  rw [win_prefix hj t z (by omega), win_suffix hj t (z+1) (by omega),rank_prefix_A] at t1
  have e : rank z 1 h (st z h+(z+1)) = 2*z+h+2 := by rw [←Nat.add_assoc,rank_suffix_B]
  rw [e] at t1
  exact t1.mpr (by omega)

end FussCover
