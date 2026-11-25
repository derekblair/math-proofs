import DelayGlobal
import Examples

namespace CoverCutoff
def uPos (i : ℕ) := 2*i
def vPos (i : ℕ) := 2*i+1
def smallU {α : Type} (f : ℕ→α) (i : ℕ) := f (uPos i)
def smallV {α : Type} (f : ℕ→α) (i : ℕ) := f (vPos i)

def CatalanRows {α : Type} [LT α] (r : ℕ→α) (j : ℕ) : Prop :=
  Ascending (smallU r) 0 (j+1) ∧
  Ascending (smallV r) 0 (j+1) ∧
  ∀ t, t < j → smallU r (t+1) < smallV r t

lemma fitsSmall {j : ℕ}
    (p : Equiv.Perm (Fin (nVerts 4 2 j))) (t : Fin j) :
    (∀ a b : Fin 4, p (window t a) < p (window t b) ↔ patternA a < patternA b) ↔
    smallU (readRank p) t.val < smallU (readRank p) (t.val+1) ∧
    smallU (readRank p) (t.val+1) < smallV (readRank p) t.val ∧
    smallV (readRank p) t.val < smallV (readRank p) (t.val+1) := by
  have e0 : (p (window (step:=2) t (0:Fin 4))).val = smallU (readRank p) t.val := by
    unfold smallU uPos
    rw [show 2*t.val=(window (step:=2) t (0:Fin 4)).val by simp [window,Nat.mul_comm]]
    exact (readRank_fin p _).symm
  have e1 : (p (window (step:=2) t (1:Fin 4))).val = smallV (readRank p) t.val := by
    unfold smallV vPos
    rw [show 2*t.val+1=(window (step:=2) t (1:Fin 4)).val by simp [window,Nat.mul_comm]]
    exact (readRank_fin p _).symm
  have e2 : (p (window (step:=2) t (2:Fin 4))).val = smallU (readRank p) (t.val+1) := by
    unfold smallU uPos
    rw [show 2*(t.val+1)=(window (step:=2) t (2:Fin 4)).val by simp [window]; omega]
    exact (readRank_fin p _).symm
  have e3 : (p (window (step:=2) t (3:Fin 4))).val = smallV (readRank p) (t.val+1) := by
    unfold smallV vPos
    rw [show 2*(t.val+1)+1=(window (step:=2) t (3:Fin 4)).val by simp [window]; omega]
    exact (readRank_fin p _).symm
  constructor
  · intro h
    have h02 := (h 0 2).mpr (by decide)
    have h21 := (h 2 1).mpr (by decide)
    have h13 := (h 1 3).mpr (by decide)
    change (p (window t (0:Fin 4))).val < (p (window t (2:Fin 4))).val at h02
    change (p (window t (2:Fin 4))).val < (p (window t (1:Fin 4))).val at h21
    change (p (window t (1:Fin 4))).val < (p (window t (3:Fin 4))).val at h13
    exact ⟨e0 ▸ e2 ▸ h02, e2 ▸ e1 ▸ h21, e1 ▸ e3 ▸ h13⟩
  · rintro ⟨h02,h21,h13⟩ a b
    have h01 : p (window t (0:Fin 4)) < p (window t (2:Fin 4)) := by
      change (p (window t (0:Fin 4))).val < (p (window t (2:Fin 4))).val
      rwa [e0,e2]
    have h12 : p (window t (2:Fin 4)) < p (window t (1:Fin 4)) := by
      change (p (window t (2:Fin 4))).val < (p (window t (1:Fin 4))).val
      rwa [e2,e1]
    have h23 : p (window t (1:Fin 4)) < p (window t (3:Fin 4)) := by
      change (p (window t (1:Fin 4))).val < (p (window t (3:Fin 4))).val
      rwa [e1,e3]
    let f : Fin 4 → Fin (nVerts 4 2 j) := fun i => p (window t (patternA.symm i))
    have hf : StrictMono f := Fin.strictMono_iff_lt_succ.mpr (by
      intro i
      fin_cases i
      · exact h01
      · exact h12
      · exact h23)
    simpa only [f,Equiv.symm_apply_apply] using (hf.lt_iff_lt (a:=patternA a) (b:=patternA b))

lemma small_packs_iff {j : ℕ} (p : Equiv.Perm (Fin (nVerts 4 2 j))) :
    Packs patternA 2 j p ↔ CatalanRows (readRank p) j := by
  constructor
  · intro h
    have hg (i : ℕ) (hi : i<j) := (fitsSmall p ⟨i,hi⟩).mp (h ⟨i,hi⟩)
    exact ⟨fun i _ hi => (hg i (by omega)).1,
      fun i _ hi => (hg i (by omega)).2.2,fun t ht => (hg t ht).2.1⟩
  · intro h t
    exact (fitsSmall p t).mpr ⟨h.1 _ (by omega) (by have := t.isLt; omega),
      h.2.2 _ t.isLt,h.2.1 _ (by omega) (by have := t.isLt; omega)⟩

#print axioms small_packs_iff
end CoverCutoff
