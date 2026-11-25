import RestrictUnique
namespace CoverCutoff

lemma ordinaryBC {r : ℕ→ℕ} {h j b c : ℕ} (hh:2≤h) (hj:1≤j) (hJ:j=h+1)
    (G : GlobalRows r h j) (hb : b<h+j-1) (hc : c<h+j-1)
    (he : ¬ (b=2*h-1 ∧ c=0)) : localB r b < localC r c := by
  by_cases hb' : b=2*h-1
  · have hc' : 1≤c := by omega
    have hx : localA r (h+1) < localC r 1 := by
      simpa [Nat.add_comm] using (G.2.2.2 1 (by omega)).2.2.2
    exact ((ab_neg hh hj G (i:=h+1) (by omega) hb).mpr (Or.inr (by omega))).trans
      (hx.trans_le (asc_le' G.2.2.1 hc hc'))
  · exact ((ab_neg hh hj G (i:=h) (by omega) hb).mpr (Or.inr (by omega))).trans
      (earlyA_C hh hj G (by omega) hc)

theorem restrict_inj_next {h j : ℕ} (hh:2≤h) (hj:1≤j) (hJ:j=h+1)
    (p q : Equiv.Perm (Fin (BigN h j)))
    (hp : Packs (delayed h hh) 3 j p) (hq : Packs (delayed h hh) 3 j q)
    (H : restrictSmall h j hh hj p = restrictSmall h j hh hj q)
    (HBC : localB (readRank p) (2*h-1) < localC (readRank p) 0 ↔
      localB (readRank q) (2*h-1) < localC (readRank q) 0) : p=q := by
  set f := readRank p
  set g := readRank q
  have P : GlobalRows f h j := (packs_iff_global hh hj p).mp hp
  have Q : GlobalRows g h j := (packs_iff_global hh hj q).mp hq
  have NB := bigSize (h:=h) hj
  have NS := smallSize hj
  have hin (a b : ℕ) (ha:a<BigN h j) (hb:b<BigN h j) (hne:a≠b) :
      f a≠f b ∧ g a≠g b :=
    ⟨fun e=>hne (readRank_inj p ha hb e),fun e=>hne (readRank_inj q ha hb e)⟩
  have ac (i c : ℕ) (hi:i<h+j) (hc:c<h+j-1) :
      localA f i < localC f c ↔ localA g i < localC g c := by
    by_cases h1 : i<h-1
    · exact iff_of_true (earlyA_C hh hj P (by omega) hc) (earlyA_C hh hj Q (by omega) hc)
    by_cases h2 : j<c
    · exact iff_of_true (allA_tailC hh hj P hi hc h2) (allA_tailC hh hj Q hi hc h2)
    have ha : uPos (i-(h-1))<SmallN j := by unfold uPos; omega
    have hb : vPos c<SmallN j := by unfold vPos; omega
    have hp' := restrict_comparison hh hj p ha hb
    have hq' := restrict_comparison hh hj q ha hb
    rw [H] at hp'
    rw [kept_U,kept_V,show h-1+(i-(h-1))=i by omega] at hp' hq'
    exact hp'.symm.trans hq'
  have bc (b c : ℕ) (hb:b<h+j-1) (hc:c<h+j-1) :
      localB f b < localC f c ↔ localB g b < localC g c := by
    by_cases he : b=2*h-1 ∧ c=0
    · obtain ⟨rfl,rfl⟩ := he
      exact HBC
    exact iff_of_true (ordinaryBC hh hj hJ P hb hc he) (ordinaryBC hh hj hJ Q hb hc he)
  have cb (b c : ℕ) (hb:b<h+j-1) (hc:c<h+j-1) :
      localC f c < localB f b ↔ localC g c < localB g b := by
    have hn := hin (posB b) (posC c) (by unfold posB; omega)
      (by unfold posC; omega) (by unfold posB posC; omega)
    exact reverse_comparison _ _ _ _ (bc b c hb hc) hn.1 hn.2
  have ca (c i : ℕ) (hc:c<h+j-1) (hi:i<h+j) :
      localC f c < localA f i ↔ localC g c < localA g i := by
    have hne := hin (posA i) (posC c) (by unfold posA; omega)
      (by unfold posC; omega) (by unfold posA posC; omega)
    exact reverse_comparison _ _ _ _ (ac i c hi hc) hne.1 hne.2
  apply same_comparisons
  intro x y
  let a := x.val
  let b := y.val
  have ha : a<BigN h j := x.isLt
  have hb : b<BigN h j := y.isLt
  have conv : (f a<f b ↔ g a<g b) → (p x<p y ↔ q x<q y) := by
    intro hc
    change (p x).val < (p y).val ↔ (q x).val < (q y).val
    simpa only [f,g,a,b,readRank_fin] using hc
  apply conv
  have a0 : a%3=0 ∨ a%3=1 ∨ a%3=2 := by omega
  have b0 : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
  rcases a0 with a0|a0|a0 <;> rcases b0 with b0|b0|b0
  · rw [show a=posA (a/3) by unfold posA; omega,show b=posA (b/3) by unfold posA; omega]
    exact (asc_iff P.1 (by omega) (by omega)).trans (asc_iff Q.1 (by omega) (by omega)).symm
  · rw [show a=posA (a/3) by unfold posA; omega,show b=posB (b/3) by unfold posB; omega]
    exact (ab_pos hh hj P (by omega) (by omega)).trans (ab_pos hh hj Q (by omega) (by omega)).symm
  · rw [show a=posA (a/3) by unfold posA; omega,show b=posC (b/3) by unfold posC; omega]
    exact ac _ _ (by omega) (by omega)
  · rw [show a=posB (a/3) by unfold posB; omega,show b=posA (b/3) by unfold posA; omega]
    exact (ab_neg hh hj P (by omega) (by omega)).trans (ab_neg hh hj Q (by omega) (by omega)).symm
  · rw [show a=posB (a/3) by unfold posB; omega,show b=posB (b/3) by unfold posB; omega]
    exact (asc_iff P.2.1 (by omega) (by omega)).trans (asc_iff Q.2.1 (by omega) (by omega)).symm
  · rw [show a=posB (a/3) by unfold posB; omega,show b=posC (b/3) by unfold posC; omega]
    exact bc _ _ (by omega) (by omega)
  · rw [show a=posC (a/3) by unfold posC; omega,show b=posA (b/3) by unfold posA; omega]
    exact ca _ _ (by omega) (by omega)
  · rw [show a=posC (a/3) by unfold posC; omega,show b=posB (b/3) by unfold posB; omega]
    exact cb _ _ (by omega) (by omega)
  · rw [show a=posC (a/3) by unfold posC; omega,show b=posC (b/3) by unfold posC; omega]
    exact (asc_iff P.2.2.1 (by omega) (by omega)).trans (asc_iff Q.2.2.1 (by omega) (by omega)).symm

#print axioms restrict_inj_next
end CoverCutoff
