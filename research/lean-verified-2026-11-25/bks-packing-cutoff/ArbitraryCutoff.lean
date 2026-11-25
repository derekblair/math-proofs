import RestrictUnique
import DelayStrict
namespace CoverCutoff

lemma admissible_from_two {K d : ℕ} (hd:d<K) (p : Equiv.Perm (Fin K))
    (r : Equiv.Perm (Fin (nVerts K d 2))) (hr : Packs p d 2 r) :
    Admissible p d := by
  intro a b
  let castpos (v : Fin (K-d)) : Fin K := Fin.castLE (Nat.sub_le _ _) v
  let shiftpos (v : Fin (K-d)) : Fin K := ⟨d+v.val,by have := v.isLt; omega⟩
  have he (v : Fin (K-d)) : window (step:=d) (0:Fin 2) (shiftpos v) =
      window (step:=d) (1:Fin 2) (castpos v) := Fin.ext (by simp [window,shiftpos,castpos])
  have h0 := hr (0:Fin 2) (shiftpos a) (shiftpos b)
  have h1 := hr (1:Fin 2) (castpos a) (castpos b)
  rw [he,he] at h0
  exact h1.symm.trans h0

lemma delayed_admissible {h : ℕ} (hh:2≤h) : Admissible (delayed h hh) 3 := by
  let p := witnessSmall 2
  have hp : Packs patternA 2 2 p := (small_packs_iff _).mpr (witnessRow (by decide))
  exact admissible_from_two (by omega) _ (liftRanks (h:=h) p false)
    (lift_packs hh (by decide) p hp false)

/-- For every prescribed duration, two admissible pattern packings can
    agree up through that duration and disagree immediately afterward. -/
theorem arbitrary_delay {h : ℕ} (hh:2≤h) :
    ∃ (K : ℕ) (p : Equiv.Perm (Fin K)),
      3 < K ∧ Admissible p 3 ∧
      (∀ j, 1≤j → j≤h → packCount patternA 2 j = packCount p 3 j) ∧
      packCount patternA 2 (h+1) < packCount p 3 (h+1) :=
  ⟨3*h+1,delayed h hh,by omega,delayed_admissible hh,
    fun _ hj hJ => same_counts_below hh hj hJ,delayed_strict hh⟩

/-- A constant uniform cutoff independent of pattern lengths, even
    restricting to admissible patterns and step at least two. -/
def UniformCutoff (B : ℕ) : Prop :=
  ∀ {k l : ℕ} (p : Equiv.Perm (Fin k)) (q : Equiv.Perm (Fin l))
    (d e : ℕ), 2≤d → d<k → 2≤e → e<l →
    Admissible p d → Admissible q e →
    (∀ j, 1≤j → j≤B → packCount p d j = packCount q e j) →
    ∀ j, 1≤j → packCount p d j = packCount q e j

theorem no_uniform_cutoff : ¬ ∃ B, UniformCutoff B := by
  rintro ⟨B,H⟩
  let h := max B 2
  have hb : B≤h := le_max_left _ _
  obtain ⟨K,p,hK,hP,hSame,hStrict⟩ := arbitrary_delay (h:=h) (le_max_right _ _)
  have he := H patternA p 2 3 (by decide) (by decide) (by decide) hK admissibleA hP
    (fun j hj hj' => hSame j hj (hj'.trans hb)) (h+1) (by omega)
  omega

#print axioms arbitrary_delay
#print axioms no_uniform_cutoff
end CoverCutoff
