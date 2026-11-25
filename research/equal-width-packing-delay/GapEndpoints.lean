import FiberCount
namespace CoverCutoff

variable {h : ℕ}

lemma gap_row (p : GapPack h) : CatalanRows (readRank p.val.val) (h+1) :=
  (small_packs_iff _).mp p.val.prop

lemma gap_initial_chain (p : GapPack h) :
    smallU (readRank p.val.val) 0 < smallU (readRank p.val.val) 1 ∧
    smallU (readRank p.val.val) 1 < smallV (readRank p.val.val) 0 ∧
    smallV (readRank p.val.val) 0 < smallU (readRank p.val.val) 2 :=
  ⟨(gap_row p).1 0 (by omega) (by omega),(gap_row p).2.2 0 (by omega),p.prop⟩

lemma gap_remaining_gt (hh : 2≤h) (p : GapPack h)
    (v : ℕ) (hv : v < SmallN (h+1)) (hn0 : v≠uPos 0)
    (hn1 : v≠uPos 1) (hn2 : v≠vPos 0) :
    smallV (readRank p.val.val) 0 < readRank p.val.val v := by
  have N := smallSize (j:=h+1) (by omega)
  have R := gap_row p
  by_cases he : v%2=0
  · have e : v=uPos (v/2) := by unfold uPos; omega
    have hi : 2≤v/2 := by unfold uPos at hn0 hn1; omega
    rw [e]
    exact p.prop.trans_le (asc_le' R.1 (by omega) hi)
  · have e : v=vPos (v/2) := by unfold vPos; omega
    have hi : 0<v/2 := by unfold vPos at hn2; omega
    rw [e]
    exact (asc_iff R.2.1 (i:=0) (k:=v/2) (by omega) (by omega)).mpr hi

lemma gap_first_ranks (hh : 2≤h) (p : GapPack h) :
    smallU (readRank p.val.val) 0 = 0 ∧
    smallU (readRank p.val.val) 1 = 1 ∧
    smallV (readRank p.val.val) 0 = 2 := by
  have N := smallSize (j:=h+1) (by omega)
  have H := gap_initial_chain p
  let r := p.val.val
  let x := r.symm ⟨2,by omega⟩
  have e : readRank r x.val=2 := by
    rw [readRank_fin]
    simp [x]
  have X : x.val < SmallN (h+1) := x.isLt
  have hx : smallV (readRank r) 0 ≤ 2 := by
    by_cases h0 : x.val=uPos 0
    · rw [h0] at e
      change smallU (readRank r) 0 = 2 at e
      change smallU (readRank r) 0 < smallU (readRank r) 1 ∧
        smallU (readRank r) 1 < smallV (readRank r) 0 ∧
        smallV (readRank r) 0 < smallU (readRank r) 2 at H
      let y := r.symm ⟨0,by omega⟩
      have ey : readRank r y.val=0 := by rw [readRank_fin]; simp [y]
      have hy0 : y.val≠uPos 0 := by intro E; rw [E] at ey; change smallU (readRank r) 0=0 at ey; omega
      have hy1 : y.val≠uPos 1 := by intro E; rw [E] at ey; change smallU (readRank r) 1=0 at ey; omega
      have hy2 : y.val≠vPos 0 := by intro E; rw [E] at ey; change smallV (readRank r) 0=0 at ey; omega
      have Z := gap_remaining_gt hh p y.val y.isLt hy0 hy1 hy2
      change smallV (readRank r) 0 < readRank r y.val at Z
      omega
    by_cases h1 : x.val=uPos 1
    · rw [h1] at e
      change smallU (readRank r) 1 = 2 at e
      change smallU (readRank r) 0 < smallU (readRank r) 1 ∧
        smallU (readRank r) 1 < smallV (readRank r) 0 ∧
        smallV (readRank r) 0 < smallU (readRank r) 2 at H
      let y := r.symm ⟨1-(smallU (readRank r) 0),by omega⟩
      have ey : readRank r y.val=1-(smallU (readRank r) 0) := by rw [readRank_fin]; simp [y]
      have hy0 : y.val≠uPos 0 := by intro E; rw [E] at ey; change smallU (readRank r) 0=1-smallU (readRank r) 0 at ey; omega
      have hy1 : y.val≠uPos 1 := by intro E; rw [E] at ey; change smallU (readRank r) 1=1-smallU (readRank r) 0 at ey; omega
      have hy2 : y.val≠vPos 0 := by intro E; rw [E] at ey; change smallV (readRank r) 0=1-smallU (readRank r) 0 at ey; omega
      have Z := gap_remaining_gt hh p y.val y.isLt hy0 hy1 hy2
      change smallV (readRank r) 0 < readRank r y.val at Z
      omega
    by_cases h2 : x.val=vPos 0
    · rw [h2] at e
      exact e.le
    have Z := gap_remaining_gt hh p x.val X h0 h1 h2
    change smallV (readRank r) 0 < readRank r x.val at Z
    omega
  change smallU (readRank r) 0 < smallU (readRank r) 1 ∧
    smallU (readRank r) 1 < smallV (readRank r) 0 ∧
    smallV (readRank r) 0 < smallU (readRank r) 2 at H
  change smallU (readRank r) 0=0 ∧ smallU (readRank r) 1=1 ∧ smallV (readRank r) 0=2
  omega

lemma final_rank (hh : 2≤h) (p : SmallPack h) :
    smallV (readRank p.val) (h+1) = 2*h+3 := by
  have N := smallSize (j:=h+1) (by omega)
  let r := p.val
  let R := (small_packs_iff r).mp p.prop
  have last (v : ℕ) (hv : v<SmallN (h+1)) :
      readRank r v ≤ smallV (readRank r) (h+1) := by
    by_cases he : v%2=0
    · rw [show v=uPos (v/2) by unfold uPos; omega]
      have mid := R.2.2 h (by omega)
      exact ((asc_le' R.1 (by omega) (show v/2≤h+1 by omega)).trans mid.le).trans
        (asc_le' R.2.1 (by omega) (by omega))
    · rw [show v=vPos (v/2) by unfold vPos; omega]
      change smallV (readRank r) (v/2) ≤ smallV (readRank r) (h+1)
      exact asc_le' R.2.1 (by omega) (by omega)
  let x := r.symm ⟨2*h+3,by omega⟩
  have e : readRank r x.val=2*h+3 := by rw [readRank_fin]; simp [x]
  have lo := last x.val x.isLt
  have hi := readRank_lt r (x:=vPos (h+1)) (by unfold vPos; omega)
  change smallV (readRank r) (h+1) < SmallN (h+1) at hi
  change smallV (readRank r) (h+1) = 2*h+3
  omega

#print axioms gap_first_ranks
end CoverCutoff
