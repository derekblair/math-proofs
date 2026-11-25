import ArbitraryCutoff

namespace CoverCutoff

/-- Same width and step as delayed; the middle positions run in reverse
and form a forced initial chain in every packing. -/
def peerRank (h pos : ℕ) : ℕ :=
  let q := pos/3
  match pos%3 with
  | 0 => 2*h+q
  | 1 => h-1-q
  | _ => h+q

lemma peerRank_lt {h pos : ℕ} (hh : 0<h) (hp : pos<3*h+1) :
    peerRank h pos<3*h+1 := by
  have hm : pos%3=0 ∨ pos%3=1 ∨ pos%3=2 := by omega
  rcases hm with e|e|e <;> simp [peerRank,e] <;> omega

lemma peerRank_inj {h x y : ℕ} (hh : 0<h)
    (hx : x<3*h+1) (hy : y<3*h+1) (he : peerRank h x=peerRank h y) :
    x=y := by
  have hx' : x%3=0 ∨ x%3=1 ∨ x%3=2 := by omega
  have hy' : y%3=0 ∨ y%3=1 ∨ y%3=2 := by omega
  rcases hx' with ax|ax|ax <;> rcases hy' with ay|ay|ay <;>
    simp only [peerRank,ax,ay] at he <;> omega

noncomputable def equalWidthPeer (h : ℕ) (hh : 0<h) : Equiv.Perm (Fin (3*h+1)) :=
  Equiv.ofBijective (fun x => ⟨peerRank h x.val,peerRank_lt hh x.isLt⟩)
    ((Finite.injective_iff_bijective).mp (fun x y e => Fin.ext
      (peerRank_inj hh x.isLt y.isLt (congrArg Fin.val e))))

lemma peerRank_phase {h pos : ℕ} (hh : 0<h) (hi : pos<3*h+1) :
    (peerRank h pos< h ↔ pos%3=1) ∧
    (h≤peerRank h pos ∧ peerRank h pos<2*h ↔ pos%3=2) ∧
    (2*h≤peerRank h pos ↔ pos%3=0) := by
  have hm : pos%3=0 ∨ pos%3=1 ∨ pos%3=2 := by omega
  rcases hm with e|e|e <;> simp [peerRank,e] <;> omega

/-- Shift invariance of relative ranks on the overlap, even though one row
has the opposite orientation. -/
lemma peer_shift {h a b : ℕ} (hh : 0<h) (ha : a+3<3*h+1) (hb : b+3<3*h+1) :
    peerRank h a < peerRank h b ↔ peerRank h (a+3)<peerRank h (b+3) := by
  have aa : (a+3)%3=a%3 := by omega
  have bb : (b+3)%3=b%3 := by omega
  have da : (a+3)/3=a/3+1 := by omega
  have db : (b+3)/3=b/3+1 := by omega
  have am : a%3=0 ∨ a%3=1 ∨ a%3=2 := by omega
  have bm : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
  rcases am with x|x|x <;> rcases bm with y|y|y <;>
    simp only [peerRank,aa,bb,da,db,x,y] <;> omega

lemma peer_admissible {h : ℕ} (hh : 2≤h) : Admissible (equalWidthPeer h (by omega)) 3 := by
  intro a b
  have ai := a.isLt; have bi := b.isLt
  change peerRank h a.val < peerRank h b.val ↔ peerRank h (3+a.val)<peerRank h (3+b.val)
  have q := peer_shift (h:=h) (a:=a.val) (b:=b.val) (by omega) (by omega) (by omega)
  simpa only [Nat.add_comm 3 a.val,Nat.add_comm 3 b.val] using q

end CoverCutoff
