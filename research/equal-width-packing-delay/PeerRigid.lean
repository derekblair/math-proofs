import PeerRetract

namespace CoverCutoff

lemma asc_le {f : ℕ→ℕ} {m a b : ℕ} (A : Ascending f 0 m)
    (bl : b<m) (ab : a≤b) : f a≤f b := by
  rcases lt_or_eq_of_le ab with l|e
  · exact (asc_lt A (by omega) (by omega) l).le
  · rw [e]

lemma desc_le {f : ℕ→ℕ} {m a b : ℕ} (B : Descending f 0 m)
    (bl : b<m) (ab : a≤b) : f b≤f a := by
  rcases lt_or_eq_of_le ab with l|e
  · have X : Ascending (α:=ℕᵒᵈ) f 0 m := B
    exact (show f b<f a from asc_lt (α:=ℕᵒᵈ) X (i:=a) (j:=b) (by omega) (by omega) l).le
  · rw [e]

lemma peer_B_C {f : ℕ→ℕ} {h j b c : ℕ} (G : PeerGlobal f h j)
    (hb : b<h+j-1) (hc : c<h+j-1) : localB f b < localC f c :=
  (desc_le G.1 hb (Nat.zero_le _)).trans_lt
    (G.2.2.2.1.trans_le (asc_le G.2.1 hc (Nat.zero_le _)))

lemma peer_C_A {f : ℕ→ℕ} {h j c a : ℕ} (G : PeerGlobal f h j) (hj : 1≤j)
    (hh : 2≤h) (ca : c≤h-1) (ha : a<h+j) : localC f c < localA f a := by
  have X := G.2.2.2.2 0 (by omega)
  simp only [Nat.zero_add] at X
  exact (asc_le G.2.1 (by omega) ca).trans_lt (X.trans_le (asc_le G.2.2.1 ha (by omega)))

lemma peer_B_A {f : ℕ→ℕ} {h j b a : ℕ} (G : PeerGlobal f h j) (hj : 1≤j)
    (hh : 2≤h) (hb : b<h+j-1) (ha : a<h+j) : localB f b < localA f a :=
  (peer_B_C G hb (c:=0) (by omega)).trans (peer_C_A G hj hh (by omega) ha)

lemma peer_C_lateA {f : ℕ→ℕ} {h j c a : ℕ} (G : PeerGlobal f h j) (hj : 1≤j)
    (hh : 2≤h) (hc : c<h+j-1) (ha : a<h+j) (ha' : j-1≤a) :
    localC f c < localA f a := by
  have X := G.2.2.2.2 (j-1) (by omega)
  exact (asc_le G.2.1 (by omega) (by omega)).trans_lt
    (X.trans_le (asc_le G.2.2.1 ha ha'))

lemma asc_cmp {f : ℕ→ℕ} {m a b : ℕ} (D : Ascending f 0 m)
    (ha : a<m) (hb : b<m) : f a < f b ↔ a<b := by
  constructor
  · intro e
    by_contra! h
    exact (not_lt_of_ge (asc_le D ha h)) e
  · exact asc_lt D (by omega) (by omega)
lemma desc_cmp {f : ℕ→ℕ} {m a b : ℕ} (D : Descending f 0 m)
    (ha : a<m) (hb : b<m) : f a < f b ↔ b<a := by
  constructor
  · intro e
    by_contra! h
    exact (not_lt_of_ge (desc_le D hb h)) e
  · intro e
    have X : Ascending (α:=ℕᵒᵈ) f 0 m := D
    exact (show f a < f b from asc_lt (α:=ℕᵒᵈ) X (i:=b) (j:=a) (by omega) (by omega) e)

lemma peerB_core {f : ℕ→ℕ} {h j b : ℕ} (G : PeerGlobal f h j) (hh : 2≤h) (hj : 1≤j)
    (hb : b<h+j-1) (i : Fin (SmallN j)) : localB f b < f (peerIndex h i.val) := by
  have E := smallSize hj
  have hi := i.isLt
  unfold peerIndex
  split_ifs with d
  · exact peer_B_C G hb (by omega)
  · exact peer_B_A G hj hh hb (by omega)

lemma peerEarly_core {f : ℕ→ℕ} {h j c : ℕ} (G : PeerGlobal f h j) (hh : 2≤h) (hj : 1≤j)
    (hc : c<h-2) (i : Fin (SmallN j)) : localC f c < f (peerIndex h i.val) := by
  have E := smallSize hj
  have hi := i.isLt
  unfold peerIndex
  split_ifs with d
  · exact asc_lt G.2.1 (by omega) (by omega) (by omega)
  · exact peer_C_A G hj hh (by omega) (by omega)

lemma peerCore_late {f : ℕ→ℕ} {h j a : ℕ} (G : PeerGlobal f h j) (hh : 2≤h) (hj : 1≤j)
    (ha : a<h+j) (al : j<a) (i : Fin (SmallN j)) : f (peerIndex h i.val) < localA f a := by
  have E := smallSize hj
  have hi := i.isLt
  unfold peerIndex
  split_ifs with d
  · exact peer_C_lateA G hj hh (by omega) ha (by omega)
  · change localA f (i.val/2) < localA f a
    exact asc_lt G.2.2.1 (by omega) (by omega) (by omega)

def PeerCmp {h j : ℕ} (small : Equiv.Perm (Fin (SmallN j))) : PeerLabel h j → PeerLabel h j → Prop
  | .reverseB a, .reverseB b => b.val<a.val
  | .reverseB _, _ => True
  | .earlyC a, .earlyC b => a.val<b.val
  | .earlyC _, .core _ | .earlyC _, .lateA _ => True
  | .core a, .core b => small a<small b
  | .core _, .lateA _ => True
  | .lateA a, .lateA b => a.val<b.val
  | _,_ => False

lemma peer_cmp_rigid {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) (G : PeerGlobal (readRank p) h j)
    (a b : PeerLabel h j) :
    p (peerLabelPos hh hj a) < p (peerLabelPos hh hj b) ↔
      PeerCmp (peerRestrict h j hh hj p) a b := by
  have C (x y : Fin (BigN h j)) : p x < p y ↔ readRank p x.val < readRank p y.val := by rw [readRank_fin,readRank_fin]; rfl
  rw [C]
  cases a <;> cases b <;> rename_i a b
  all_goals simp only [peerLabelPos,PeerCmp,Fin.val_mk]
  · exact desc_cmp G.1 a.isLt b.isLt
  · exact iff_true_intro (peer_B_C G a.isLt (by have := b.isLt; omega))
  · exact iff_true_intro (peerB_core G hh hj a.isLt b)
  · exact iff_true_intro (peer_B_A G hj hh a.isLt (by have := b.isLt; omega))
  · exact iff_false_intro (not_lt_of_gt (peer_B_C G b.isLt (by have := a.isLt; omega)))
  · exact asc_cmp G.2.1 (by have := a.isLt; omega) (by have := b.isLt; omega)
  · exact iff_true_intro (peerEarly_core G hh hj a.isLt b)
  · exact iff_true_intro (peer_C_lateA G hj hh (by have := a.isLt; omega) (by have := b.isLt; omega) (by omega))
  · exact iff_false_intro (not_lt_of_gt (peerB_core G hh hj b.isLt a))
  · exact iff_false_intro (not_lt_of_gt (peerEarly_core G hh hj b.isLt a))
  · have F := (peer_restrict_cmp hh hj p a.isLt b.isLt).symm
    rw [readRank_fin,readRank_fin] at F
    exact F
  · exact iff_true_intro (peerCore_late G hh hj (by have := b.isLt; omega) (by omega) a)
  · exact iff_false_intro (not_lt_of_gt (peer_B_A G hj hh b.isLt (by have := a.isLt; omega)))
  · exact iff_false_intro (not_lt_of_gt (peer_C_lateA G hj hh (by have := b.isLt; omega) (by have := a.isLt; omega) (by omega)))
  · exact iff_false_intro (not_lt_of_gt (peerCore_late G hh hj (by have := a.isLt; omega) (by omega) b))
  · have E := asc_cmp G.2.2.1 (a:=j+1+a.val) (b:=j+1+b.val)
      (by have := a.isLt; omega) (by have := b.isLt; omega)
    exact E.trans (by omega)

end CoverCutoff
