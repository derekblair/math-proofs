import PeerRows

namespace CoverCutoff

def PeerFits (r : ℕ→ℕ) (h t : ℕ) : Prop :=
  ∀ x y, x<3*h+1 → y<3*h+1 →
    (r (3*t+x)<r (3*t+y) ↔ peerRank h x<peerRank h y)

lemma pA_rank (h i : ℕ) : peerRank h (posA i)=2*h+i := by
  have u : posA i%3=0 := by simp [posA]
  have v : posA i/3=i := by unfold posA;omega
  simp [peerRank,u,v]
lemma pB_rank (h i : ℕ) : peerRank h (posB i)=h-1-i := by
  have u : posB i%3=1 := by unfold posB;omega
  have v : posB i/3=i := by unfold posB;omega
  simp [peerRank,u,v]
lemma pC_rank (h i : ℕ) : peerRank h (posC i)=h+i := by
  have u : posC i%3=2 := by unfold posC;omega
  have v : posC i/3=i := by unfold posC;omega
  simp [peerRank,u,v]

lemma peerLocal_of_fit {h t : ℕ} {r : ℕ→ℕ} (hh : 2≤h) (D : PeerFits r h t) :
    PeerLocal r h t := by
  have HA (i : ℕ) : r (3*t+posA i)=localA r (t+i) := by unfold localA posA; congr 1; omega
  have HB (i : ℕ) : r (3*t+posB i)=localB r (t+i) := by unfold localB posB; congr 1; omega
  have HC (i : ℕ) : r (3*t+posC i)=localC r (t+i) := by unfold localC posC; congr 1; omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i ti hi
    have v := (D (posB (i+1-t)) (posB (i-t)) (by unfold posB;omega) (by unfold posB;omega)).mpr
    rw [pB_rank,pB_rank,HB,HB,show t+(i+1-t)=i+1 by omega,show t+(i-t)=i by omega] at v
    exact v (by omega)
  · intro i ti hi
    have v := (D (posC (i-t)) (posC (i+1-t)) (by unfold posC;omega) (by unfold posC;omega)).mpr
    rw [pC_rank,pC_rank,HC,HC,show t+(i+1-t)=i+1 by omega,show t+(i-t)=i by omega] at v
    exact v (by omega)
  · intro i ti hi
    have v := (D (posA (i-t)) (posA (i+1-t)) (by unfold posA;omega) (by unfold posA;omega)).mpr
    rw [pA_rank,pA_rank,HA,HA,show t+(i+1-t)=i+1 by omega,show t+(i-t)=i by omega] at v
    exact v (by omega)
  · have v := (D (posB 0) (posC 0) (by unfold posB;omega) (by unfold posC;omega)).mpr
    rw [pB_rank,pC_rank,HB,HC,Nat.add_zero] at v
    exact v (by omega)
  · have v := (D (posC (h-1)) (posA 0) (by unfold posC;omega) (by unfold posA;omega)).mpr
    rw [pC_rank,pA_rank,HC,HA,Nat.add_zero,show t+(h-1)=t+h-1 by omega] at v
    exact v (by omega)

lemma peer_window_iff {h j : ℕ} (hh : 2≤h) (t : Fin j)
    (p : Equiv.Perm (Fin (BigN h j))) :
    (∀ x y : Fin (3*h+1),
      p (window (step:=3) t x)<p (window (step:=3) t y) ↔
        equalWidthPeer h (by omega) x<equalWidthPeer h (by omega) y)
    ↔ PeerLocal (readRank p) h t.val := by
  have H (x : Fin (3*h+1)) :
      readRank p (3*t.val+x.val)=(p (window t x)).val := by
    rw [show 3*t.val+x.val=(window (step:=3) t x).val by simp [window];omega]
    exact readRank_fin p _
  constructor
  · intro P
    apply peerLocal_of_fit hh
    intro x y hx hy
    rw [H ⟨x,hx⟩,H ⟨y,hy⟩]
    exact P ⟨x,hx⟩ ⟨y,hy⟩
  · intro Q x y
    let r := equalWidthPeer h (by omega)
    let f : Fin (3*h+1) → Fin (BigN h j) := fun z => p (window t (r.symm z))
    have F : StrictMono f := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro u
      change (p (window t (r.symm u.castSucc))).val < (p (window t (r.symm u.succ))).val
      rw [←H,←H,peer_inv_val hh,peer_inv_val hh]
      exact peerLocal_adj hh Q u.val u.isLt
    simpa only [f,Equiv.symm_apply_apply] using (F.lt_iff_lt (a:=r x) (b:=r y))

lemma peer_packs_iff {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) :
    Packs (equalWidthPeer h (by omega)) 3 j p ↔ PeerGlobal (readRank p) h j := by
  rw [←gl_peers hh hj]
  constructor
  · intro P t ht; exact (peer_window_iff hh ⟨t,ht⟩ p).mp (P ⟨t,ht⟩)
  · intro P t; exact (peer_window_iff hh t p).mpr (P t.val t.isLt)

end CoverCutoff
