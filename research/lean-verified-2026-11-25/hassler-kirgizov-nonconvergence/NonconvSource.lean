import NonconvRealize
import NonconvWalk

namespace Nonconv
open Emerging

noncomputable def permWord (u : State) : Perm 9 :=
  Equiv.ofBijective
    (fun i => ⟨word u i.val-1,by have hh := valid_word u i; omega⟩)
    (Finite.injective_iff_bijective.mp (fun i j e => by
      apply injective_word u i j
      have hi := (valid_word u i).1
      have hj := (valid_word u j).1
      have hh := congrArg Fin.val e
      change word u i.val-1=word u j.val-1 at hh
      omega))

lemma word_occurs {n : Nat} (f : Perm n) (i : Nat) (u : State) :
    occurs f i (permWord u) ↔ Matches (ext f) i u := by
  constructor
  · intro h a ha b hb
    have hh := h ⟨b,hb⟩ ⟨a,ha⟩
    change (_ ↔ word u b-1 < word u a-1) at hh
    have h1 := (valid_word u ⟨a,ha⟩).1
    have h2 := (valid_word u ⟨b,hb⟩).1
    dsimp only at h1 h2
    have he : word u b-1 < word u a-1 ↔ word u b < word u a := by omega
    rwa [he] at hh
  · intro h a b
    have hh := h b.val b.isLt a.val a.isLt
    change _ ↔ word u a.val-1 < word u b.val-1
    have h1 := (valid_word u a).1
    have h2 := (valid_word u b).1
    have he : word u a.val-1 < word u b.val-1 ↔ word u a.val < word u b.val := by omega
    rwa [he]

lemma match_unique (f : Nat → Nat) (i : Nat) (u v : State) (a : Matches f i u) (b : Matches f i v) : u=v := by
  apply distinct_words
  intro x y
  exact (a x.val x.isLt y.val y.isLt).symm.trans (b x.val x.isLt y.val y.isLt)

noncomputable def forbidden9 : Finset (Perm 9) := by
  classical exact Finset.univ \ Finset.univ.image permWord

lemma allowed9 (p : Perm 9) : p ∉ forbidden9 ↔ ∃ u, permWord u=p := by
  classical
  simp [forbidden9]

lemma avoids_iff_matches {n : Nat} (f : Perm n) :
    avoids f forbidden9 ↔ ∀ i, i+8<n → ∃ u : State, Matches (ext f) i u := by
  constructor
  · intro h i hi
    obtain ⟨p,hp⟩ := occurs_exists n 9 f i (by omega)
    have hnp : p ∉ forbidden9 := fun hpf => h p hpf ⟨i,by omega⟩ hp
    obtain ⟨u,rfl⟩ := (allowed9 _).mp hnp
    exact ⟨u,(word_occurs _ _ _).mp hp⟩
  · intro h p hp i ho
    obtain ⟨u,hu⟩ := h i.val (by have hi := i.isLt; omega)
    have hw := occurs_unique _ _ _ _ _ _ ho ((word_occurs _ _ _).mpr hu)
    exact ((allowed9 p).mpr ⟨u,hw.symm⟩) hp

lemma same_route_perm {m : Nat} (u : Fin (m+1) → State) (f g : Perm (m+9))
    (hf : ∀ l ≤ m, Matches (ext f) l (tagExt u l))
    (hg : ∀ l ≤ m, Matches (ext g) l (tagExt u l)) : f=g := by
  apply occurs_unique (m+9) (m+9) f 0
  · intro i j
    simpa [ext, i.isLt, j.isLt, ←Fin.lt_def]
  · intro i j
    simp only [occurs,Nat.zero_add]
    rw [Fin.lt_def]
    have ss : (g i).val = ext g i.val := by simp [ext,i.isLt]
    have tt : (g j).val = ext g j.val := by simp [ext,j.isLt]
    rw [ss,tt]
    have hi := i.isLt
    have hj := j.isLt
    by_cases hh : i.val ≤ j.val+8 ∧ j.val ≤ i.val+8
    · let l := min (min i.val j.val) m
      have hL : l ≤ m ∧ l ≤ i.val ∧ l ≤ j.val ∧ i.val<l+9 ∧ j.val<l+9 := by
        dsimp [l]
        simp only [Nat.min_def]
        split <;> split <;> omega
      have hfi := hf l hL.1 (j.val-l) (by omega) (i.val-l) (by omega)
      have hgi := hg l hL.1 (j.val-l) (by omega) (i.val-l) (by omega)
      rw [show l+(j.val-l)=j.val by omega,show l+(i.val-l)=i.val by omega] at hfi hgi
      exact hfi.trans hgi.symm
    · have hff : ∀ l < m+9-8, Matches (ext f) l (tagExt u l) := fun l hl => hf l (by omega)
      have hgg : ∀ l < m+9-8, Matches (ext g) l (tagExt u l) := fun l hl => hg l (by omega)
      by_cases hlt : i.val < j.val
      · have hb : block (row (tagExt u 0)).phase i.val < block (row (tagExt u 0)).phase j.val := by
          unfold block; omega
        have fwd := allCross (ext f) (m+9) (by omega) (tagExt u) hff _ _ hj hb
        have bwd := allCross (ext g) (m+9) (by omega) (tagExt u) hgg _ _ hj hb
        split_ifs at fwd bwd <;> omega
      · have hb : block (row (tagExt u 0)).phase j.val < block (row (tagExt u 0)).phase i.val := by
          unfold block; omega
        have fwd := allCross (ext f) (m+9) (by omega) (tagExt u) hff _ _ hi hb
        have bwd := allCross (ext g) (m+9) (by omega) (tagExt u) hgg _ _ hi hb
        split_ifs at fwd bwd <;> omega

abbrev Avoiders (m : Nat) := {f : Perm (m+9) // avoids f forbidden9}

noncomputable def routeOf (m : Nat) (f : Avoiders m) : Route false m := by
  let g := (avoids_iff_matches f.val).mp f.property
  let p : Fin (m+1) → State := fun i => Classical.choose (g i.val (by have := i.isLt; omega))
  have hp (i : Fin (m+1)) : Matches (ext f.val) i.val (p i) := Classical.choose_spec (g i.val (by have := i.isLt; omega))
  refine ⟨p,?_⟩
  intro i
  change edge (p i.castSucc) (p i.succ)=true
  apply decide_eq_true
  exact actualKeys (ext f.val) i.val _ _ (hp i.castSucc) (hp i.succ)

lemma matches_routeOf (m : Nat) (f : Avoiders m) (i : Nat) (hi : i ≤ m) :
    Matches (ext f.val) i (tagExt (routeOf m f).val i) := by
  have hit : i<m+1 := by omega
  simp only [tagExt,dif_pos hit,routeOf]
  exact Classical.choose_spec ((avoids_iff_matches f.val).mp f.property i (by omega))

noncomputable def permOf (m : Nat) (u : Route false m) : Avoiders m := by
  have hh := realizes u.val u.property
  refine ⟨Classical.choose hh,?_⟩
  apply (avoids_iff_matches _).mpr
  intro i hi
  exact ⟨tagExt u.val i,Classical.choose_spec hh i (by omega)⟩

lemma matches_permOf (m : Nat) (u : Route false m) (i : Nat) (hi : i ≤ m) :
    Matches (ext (permOf m u).val) i (tagExt u.val i) :=
  Classical.choose_spec (realizes u.val u.property) i hi

noncomputable def pathsPerms (m : Nat) : Avoiders m ≃ Route false m where
  toFun := routeOf m
  invFun := permOf m
  left_inv f := Subtype.ext (same_route_perm _ _ _ (matches_permOf m (routeOf m f)) (matches_routeOf m f))
  right_inv u := by
    apply Subtype.ext
    funext x
    have hA := matches_routeOf m (permOf m u) x.val (by have := x.isLt; omega)
    have hB := matches_permOf m u x.val (by have := x.isLt; omega)
    have H := match_unique _ _ _ _ hA hB
    simpa [tagExt,x.isLt] using H

end Nonconv
