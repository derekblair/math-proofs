import BallotToPack

namespace FussCover
open CoverCutoff Finset
variable {z h j : ℕ} (hj : 0<j) (hz : 0<z)
variable (S : BallotSet j)

lemma ballot_order : CoreOrder hj hz (ranksOfBallot (z:=z) (h:=h) hj hz S) := by
  let r := ranksOfBallot (z:=z) (h:=h) hj hz S
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a b e
    change (r (hAt hj hz a)).val < (r (hAt hj hz b)).val
    change a.val < b.val at e
    rw [ballot_head,ballot_head]
    exact e
  · intro a t
    change (r (hAt hj hz a)).val < (r (A hj t)).val
    rw [ballot_head]
    rcases allA t with e|⟨i,e⟩
    · rw [e,ballot_a0]
      exact a.isLt
    · rw [e,ballot_a]
      change a.val<hN z h j+1+(ballotU S i).val
      have := a.isLt
      omega
  · intro t
    have c : t.castSucc=aI t.rev := by simp [aI]
    change r (A hj t.succ) < r (A hj t.castSucc)
    rw [c,ballot_a]
    rcases allA t.succ with e|⟨i,e⟩
    · change (r (A hj t.succ)).val < (raise hj (ballotU S t.rev)).val
      rw [e,ballot_a0]
      change hN z h j < hN z h j+1+(ballotU S t.rev).val
      omega
    · rw [e,ballot_a]
      apply raise_mono hj
      apply U_strict
      apply aI_anti.lt_iff_gt.mp
      rw [←e,←c]
      exact Fin.castSucc_lt_succ
  · intro t
    have a : t.castSucc=aI t.rev := by simp [aI]
    have b : t.succ=bI t.rev := by simp [bI]
    change r (A hj t.castSucc) < r (B hj t.succ)
    rw [a,b,ballot_a,ballot_b]
    exact raise_mono hj (ballotCross S t.rev)
  · intro t
    have c : t.succ=bI t.rev := by simp [bI]
    change r (B hj t.succ) < r (B hj t.castSucc)
    rw [c,ballot_b]
    rcases allB t.castSucc with e|⟨i,e⟩
    · change (raise hj (ballotD S t.rev)).val < (r (B hj t.castSucc)).val
      rw [e,ballot_b0]
      change hN z h j+1+(ballotD S t.rev).val < hN z h j+2*j+1
      have := (ballotD S t.rev).isLt
      omega
    · rw [e,ballot_b]
      apply raise_mono hj
      apply D_strict
      apply bI_anti.lt_iff_gt.mp
      rw [←c,←e]
      exact Fin.castSucc_lt_succ

noncomputable def ballotToPack :
    {r : Equiv.Perm (Fin (n z h j)) // packed r} :=
  ⟨ranksOfBallot hj hz S,order_to_packed hj hz _ (ballot_order hj hz S)⟩

lemma ballot_right :
    packToBallot hj hz (ballotToPack (z:=z) (h:=h) hj hz S) = S := by
  let r := ranksOfBallot (z:=z) (h:=h) hj hz S
  let P : packed r := (ballotToPack (z:=z) (h:=h) hj hz S).2
  have rr (i : Fin j) : U hj hz r P i = ballotU S i := by
    apply (raise_mono (z:=z) (h:=h) hj).injective
    exact (raise_U hj hz r P i).trans (ballot_a hj hz S i)
  apply Subtype.ext
  change upRanks hj hz r P = S.val
  unfold upRanks
  rw [show U hj hz r P = ballotU S from funext rr]
  exact image_orderEmbOfFin_univ _ _

lemma ballot_left (p : {r : Equiv.Perm (Fin (n z h j)) // packed r}) :
    ballotToPack hj hz (packToBallot hj hz p) = p := by
  let S := packToBallot hj hz p
  let rr := ranksOfBallot (z:=z) (h:=h) hj hz S
  let e := posEquiv (z:=z) (h:=h) hj hz
  apply Subtype.ext
  apply Equiv.ext
  intro v
  obtain ⟨w,rfl⟩ := e.surjective v
  change rr (e w) = p.1 (e w)
  cases w with
  | inl u =>
    change rr (hAt hj hz u)=p.1 (hAt hj hz u)
    apply Fin.ext
    rw [ballot_head,head_rank hj hz p.1 p.2]
  | inr x =>
    cases x with
    | inl t =>
      change rr (A hj t)=p.1 (A hj t)
      rcases allA t with E|⟨i,E⟩
      · apply Fin.ext; rw [E,ballot_a0,A_last_rank hj hz p.1 p.2]
      · rw [E,ballot_a]
        have I : ballotU S i = U hj hz p.1 p.2 i := congrFun (up_order hj hz p.1 p.2) i
        rw [I,raise_U]
    | inr t =>
      change rr (B hj t)=p.1 (B hj t)
      rcases allB t with E|⟨i,E⟩
      · apply Fin.ext; rw [E,ballot_b0,B_first_rank hj hz p.1 p.2]
      · rw [E,ballot_b]
        have I : ballotD S i = D hj hz p.1 p.2 i := congrFun (down_order hj hz p.1 p.2) i
        rw [I,raise_D]

noncomputable def packBallotEquiv :
    {r : Equiv.Perm (Fin (n z h j)) // packed r} ≃ BallotSet j :=
  ⟨packToBallot hj hz,ballotToPack hj hz,ballot_left hj hz,ballot_right hj hz⟩

theorem packed_catalan (z h j : ℕ) (hz : 0<z) (hj : 0<j) :
    packCount (pattern z 1 h (by decide)) (st z h) j = catalan j :=
  (Nat.card_congr (packBallotEquiv (z:=z) (h:=h) hj hz)).trans (ballot_count j)

/-- The Catalan part of Blitvić–Kammoun–Steingrímsson Part I, §7 item 6.
For every overlap m>2 and every length K>2m one pattern works for
all positive numbers of prescribed, equally-spaced occurrences. -/
theorem uniform_catalan_pattern (m K : ℕ) (hm : 2<m) (hK : 2*m<K) :
    ∃ p : Equiv.Perm (Fin K),
      (∀ a b : Fin m, (p ⟨a.val,by omega⟩ < p ⟨b.val,by omega⟩) ↔
          p ⟨K-m+a.val,by have := a.isLt; omega⟩ < p ⟨K-m+b.val,by have := b.isLt; omega⟩) ∧
      ∀ j > 0, packCount p (K-m) j = catalan j := by
  let z := m-2
  let h := K-2*m
  have eqK : width z 1 h=K := by unfold width; dsimp only [z,h]; omega
  have stepK : st z h=K-m := by rw [st_def]; dsimp only [z,h]; omega
  have eqm : m=z+2 := by dsimp only [z]; omega
  have eqWh : wi z h=K := eqK
  let p := pattern z 1 h (by decide)
  let E := finCongr eqK
  refine ⟨(E.symm.trans p).trans E, ?_, ?_⟩
  · intro a b
    -- Both halves are increasing in their physical index by the explicit ranks.
    have h1 (i : ℕ) (hi : i<z+2) :
        rank z 1 h i = (if i<z then i else if i=z then 2*z+h+1 else 2*z+h+3) := by
      by_cases x : i<z
      · simp [rank_prefix_low x,x]
      by_cases e : i=z
      · subst i; simp [rank_prefix_A]
      have e' : i=z+1 := by omega
      subst i; rw [rank_prefix_B]
      split_ifs ;  omega
    have h2 (i : ℕ) (hi : i<z+2) :
        rank z 1 h (st z h+i) = (if i<z then z+h+i else if i=z then 2*z+h else 2*z+h+2) := by
      by_cases x : i<z
      · simp [rank_suffix_low (⟨i,x⟩ : Fin z),x]
      by_cases e : i=z
      · subst i; simp [rank_suffix_A]
      have e' : i=z+1 := by omega
      subst i; rw [←Nat.add_assoc,rank_suffix_B]
      split_ifs ;  omega
    change rank z 1 h a.val < rank z 1 h b.val ↔
       rank z 1 h (K-m+a.val) < rank z 1 h (K-m+b.val)
    rw [←stepK,h1 a.val (by have := a.isLt; omega),h1 b.val (by have := b.isLt; omega),
          h2 a.val (by have := a.isLt; omega),h2 b.val (by have := b.isLt; omega)]
    split_ifs <;> omega
  · intro j hj
    have out := packed_catalan z h j (by dsimp [z]; omega) hj
    -- transport the pattern and its window width along the single arithmetic equality
    have trans (k K' : ℕ) (e : k=K') (p' : Equiv.Perm (Fin k)) (s : ℕ) :
        packCount (((finCongr e).symm.trans p').trans (finCongr e)) s j = packCount p' s j := by
      subst K'; rfl
    rw [trans,←stepK]
    exact out

#print axioms uniform_catalan_pattern
end FussCover
