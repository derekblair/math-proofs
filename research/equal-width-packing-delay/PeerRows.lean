import PeerPattern

namespace CoverCutoff

def Descending (f : ℕ→ℕ) (a n : ℕ) :=
  ∀ i : ℕ, a ≤ i → i + 1 < a + n → f (i + 1) < f i

def PeerLocal (r : ℕ→ℕ) (h t : ℕ) : Prop :=
  Descending (localB r) t h ∧ Ascending (localC r) t h ∧
  Ascending (localA r) t (h+1) ∧ localB r t<localC r t ∧
  localC r (t+h-1)<localA r t

def PeerGlobal (r : ℕ→ℕ) (h j : ℕ) : Prop :=
  Descending (localB r) 0 (h+j-1) ∧ Ascending (localC r) 0 (h+j-1) ∧
  Ascending (localA r) 0 (h+j) ∧ localB r 0<localC r 0 ∧
  ∀ t, t<j → localC r (t+h-1)<localA r t

lemma gl_peers {r : ℕ→ℕ} {h j : ℕ} (hh : 2≤h) (hj : 1≤j) :
    (∀ t, t<j → PeerLocal r h t) ↔ PeerGlobal r h j := by
  constructor
  · intro hL
    refine ⟨?_,?_,?_,(hL 0 (by omega)).2.2.2.1,fun t ht => (hL t ht).2.2.2.2⟩
    all_goals
      intro i _ E
      let t := min i (j-1)
      have ti : t ≤ i := min_le_left _ _
      have tJ : t < j := by dsimp [t]; omega
      first
      | exact (hL t tJ).1 i ti (by dsimp [t]; omega)
      | exact (hL t tJ).2.1 i ti (by dsimp [t]; omega)
      | exact (hL t tJ).2.2.1 i ti (by dsimp [t]; omega)
  · rintro ⟨B,C,A,H,X⟩ t ht
    refine ⟨fun i _ hi => B i (by omega) (by omega),
            fun i _ hi => C i (by omega) (by omega),
            fun i _ hi => A i (by omega) (by omega),?_,X t ht⟩
    have hb : localB r t ≤ localB r 0 := by
      by_cases e : t=0
      · simp [e]
      · have BD : Ascending (α:=ℕᵒᵈ) (localB r) 0 (h+j-1) := B
        have K := asc_lt BD (i:=0) (j:=t) (by omega) (by omega) (by omega)
        exact (show localB r t<localB r 0 from K).le
    have hc : localC r 0 ≤ localC r t := by
      by_cases e : t=0
      · simp [e]
      · exact (asc_lt C (i:=0) (j:=t) (by omega) (by omega) (by omega)).le
    exact hb.trans_lt (H.trans_le hc)

def peerInv (h u : ℕ) : ℕ :=
    if u<h then posB (h-1-u)
    else if u<2*h then posC (u-h)
    else posA (u-2*h)

lemma peerInv_bound {h q : ℕ} (_hh : 2≤h) (hq : q<3*h+1) : peerInv h q<3*h+1 := by
  unfold peerInv posA posB posC
  split_ifs <;> omega
lemma peerInv_spec {h q : ℕ} (_hh : 2≤h) (_hq : q<3*h+1) : peerRank h (peerInv h q)=q := by
  unfold peerInv
  split_ifs with B C
  · have u : posB (h-1-q)%3=1 := by unfold posB;omega
    have v : posB (h-1-q)/3=h-1-q := by unfold posB;omega
    simp only [peerRank,u,v]; omega
  · have u : posC (q-h)%3=2 := by unfold posC;omega
    have v : posC (q-h)/3=q-h := by unfold posC;omega
    simp only [peerRank,u,v]; omega
  · have u : posA (q-2*h)%3=0 := by unfold posA;omega
    have v : posA (q-2*h)/3=q-2*h := by unfold posA;omega
    simp only [peerRank,u,v]; omega

lemma peer_inv_val {h : ℕ} (hh : 2≤h) (u : Fin (3*h+1)) :
    ((equalWidthPeer h (by omega)).symm u).val=peerInv h u.val := by
  let x : Fin (3*h+1) := ⟨_,peerInv_bound hh u.isLt⟩
  have e : equalWidthPeer h (by omega) x = u := Fin.ext (peerInv_spec hh u.isLt)
  have q := congrArg (equalWidthPeer h (by omega)).symm e
  simpa only [Equiv.symm_apply_apply] using (congrArg Fin.val q).symm

lemma peerLocal_adj {r : ℕ→ℕ} {h t : ℕ} (hh : 2≤h) (P : PeerLocal r h t) :
    ∀ u<3*h, r (3*t+peerInv h u) < r (3*t+peerInv h (u+1)) := by
  intro u he
  obtain ⟨B,C,A,Q,R⟩ := P
  have HA (i : ℕ) : r (3*t+posA i)=localA r (t+i) := by unfold localA posA; congr 1; omega
  have HB (i : ℕ) : r (3*t+posB i)=localB r (t+i) := by unfold localB posB; congr 1; omega
  have HC (i : ℕ) : r (3*t+posC i)=localC r (t+i) := by unfold localC posC; congr 1; omega
  unfold peerInv
  split_ifs at * <;> simp only [HA,HB,HC] <;>
    first
    | omega
    | (rw [show t+(h-1-u)=t+(h-1-(u+1))+1 by omega]; exact B _ (by omega) (by omega))
    | (convert Q using 2 <;> omega)
    | (rw [show t+(u+1-h)=t+(u-h)+1 by omega]; exact C _ (by omega) (by omega))
    | (convert R using 2 <;> omega)
    | (rw [show t+(u+1-2*h)=t+(u-2*h)+1 by omega]; exact A _ (by omega) (by omega))

end CoverCutoff
