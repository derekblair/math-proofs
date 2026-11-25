import LiftRetract
namespace CoverCutoff

lemma asc_iff {f : ℕ→ℕ} {n i k : ℕ} (H : Ascending f 0 n) (hi : i<n) (hk : k<n) :
    f i < f k ↔ i<k := by
  have aux (x y : ℕ) (hy : y<n) (hxy : x<y) : f x < f y :=
    asc_lt H (Nat.zero_le _) (by omega) hxy
  refine ⟨?_,fun hh=>aux i k hk hh⟩
  intro h
  by_contra! q
  rcases lt_or_eq_of_le q with q|rfl
  · exact (not_lt_of_ge (aux k i hi q).le) h
  · exact (Nat.lt_irrefl _) h

lemma asc_le' {f : ℕ→ℕ} {n i k : ℕ} (H : Ascending f 0 n) (hk : k<n) (h : i≤k) :
    f i≤f k := by
  rcases lt_or_eq_of_le h with h|rfl
  · exact ((asc_iff H (by omega) hk).mpr h).le
  · exact le_rfl

lemma ab_pos {r : ℕ→ℕ} {h j i b : ℕ} (hh:2≤h) (hj:1≤j)
    (G : GlobalRows r h j) (hi : i<h+j) (hb : b<h+j-1) :
    localA r i < localB r b ↔ h-1≤b ∧ i ≤ b-(h-1) := by
  have H := (altRows_iff_global hh hj).mpr G
  by_cases he : b<h-1
  · have hB : localB r b ≤ localB r (h-2) := asc_le' G.2.1 (by omega) (by omega)
    have hA : localA r 0 ≤ localA r i := asc_le' G.1 hi (by omega)
    have hbad := (hB.trans_lt H.2.2.2.1).trans_le hA
    exact iff_of_false (by omega) (by omega)
  · have ht : b-(h-1)<j := by omega
    have Ht := H.2.2.2.2 (b-(h-1)) ht
    have hb' : b-(h-1)+h-1=b := by omega
    rw [hb'] at Ht
    refine ⟨fun hab => ⟨by omega,?_⟩,fun h => ?_⟩
    · by_contra! hl
      have hm : localA r (b-(h-1)+1)≤localA r i := asc_le' G.1 hi (by omega)
      exact (not_lt_of_ge (Ht.2.1.le.trans hm)) hab
    · exact (asc_le' G.1 (by omega) h.2).trans_lt Ht.1

lemma ab_neg {r : ℕ→ℕ} {h j i b : ℕ} (hh:2≤h) (hj:1≤j)
    (G : GlobalRows r h j) (hi : i<h+j) (hb : b<h+j-1) :
    localB r b < localA r i ↔ b<h-1 ∨ b-(h-1) < i := by
  have H := (altRows_iff_global hh hj).mpr G
  refine ⟨?_,?_⟩
  · intro h
    by_contra! he
    have hp := (ab_pos hh hj G hi hb).mpr ⟨he.1,he.2⟩
    exact (not_lt_of_ge hp.le) h
  · intro hx
    rcases hx with ha|ha
    · have hB : localB r b ≤ localB r (h-2) := asc_le' G.2.1 (by omega) (by omega)
      have hA : localA r 0 ≤ localA r i := asc_le' G.1 hi (by omega)
      exact (hB.trans_lt H.2.2.2.1).trans_le hA
    · by_cases he : b<h-1
      · have hB : localB r b ≤ localB r (h-2) := asc_le' G.2.1 (by omega) (by omega)
        exact (hB.trans_lt H.2.2.2.1).trans_le (asc_le' G.1 hi (by omega))
      · have Ht := H.2.2.2.2 (b-(h-1)) (by omega)
        have hb' : b-(h-1)+h-1=b := by omega
        rw [hb'] at Ht
        exact Ht.2.1.trans_le (asc_le' G.1 hi (by omega))

lemma earlyA_C {r : ℕ→ℕ} {h j i c : ℕ} (hh:2≤h) (hj:1≤j)
    (G : GlobalRows r h j) (hi : i≤h) (hc : c<h+j-1) :
    localA r i < localC r c := by
  have hAC := (G.2.2.2 0 (by omega)).2.2.2
  have hAC' : localA r h < localC r 0 := by simpa using hAC
  exact ((asc_le' G.1 (by omega) hi).trans_lt hAC').trans_le (asc_le' G.2.2.1 hc (by omega))

lemma allB_C {r : ℕ→ℕ} {h j b c : ℕ} (hh:2≤h) (hj:1≤j) (hJ:j≤h)
    (G : GlobalRows r h j) (hb : b<h+j-1) (hc : c<h+j-1) :
    localB r b < localC r c := by
  exact ((ab_neg hh hj G (i:=j) (by omega) hb).mpr (Or.inr (by omega))).trans
    (earlyA_C hh hj G hJ hc)

lemma allA_tailC {r : ℕ→ℕ} {h j i c : ℕ} (hh:2≤h) (hj:1≤j)
    (G : GlobalRows r h j) (hi:i<h+j) (hc:c<h+j-1) (ht:j<c) :
    localA r i < localC r c := by
  have hx := (G.2.2.2 (j-1) (by omega)).2.2.2
  exact ((asc_le' G.1 (by omega) (show i≤j-1+h by omega)).trans_lt hx).trans_le
    (asc_le' G.2.2.1 hc (by omega))

#print axioms allA_tailC
end CoverCutoff
