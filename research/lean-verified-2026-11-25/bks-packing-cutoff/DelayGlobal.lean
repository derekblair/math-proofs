import DelayWindow

namespace CoverCutoff

def GlobalRows {α : Type} [LT α] (r : ℕ→α) (h j : ℕ) : Prop :=
  Ascending (localA r) 0 (h+j) ∧
  Ascending (localB r) 0 (h+j-1) ∧
  Ascending (localC r) 0 (h+j-1) ∧
  ∀ t, t < j →
    localB r (t+h-2) < localA r t ∧
    localA r t < localB r (t+h-1) ∧
    localB r (t+h-1) < localA r (t+1) ∧
    localA r (t+h) < localC r t

lemma global_of_local {α : Type} [LT α] {r : ℕ→α} {h j : ℕ} (hj : 1≤j)
    (hh : 2≤h) (hL : ∀ t, t < j → LocalRows r h t) : GlobalRows r h j := by
  refine ⟨?_,?_,?_,fun t ht => (hL t ht).2.2.2⟩
  · intro i hi hi'
    let t := min i (j-1)
    have hj' : t<j := by dsimp [t]; omega
    have hti : t ≤ i := min_le_left _ _
    have htop : i+1<t+(h+1) := by dsimp [t]; omega
    exact (hL t hj').1 i hti htop
  · intro i hi hi'
    let t := min i (j-1)
    have hj' : t<j := by dsimp [t]; omega
    have hti : t ≤ i := min_le_left _ _
    have htop : i+1<t+h := by dsimp [t]; omega
    exact (hL t hj').2.1 i hti htop
  · intro i hi hi'
    let t := min i (j-1)
    have hj' : t<j := by dsimp [t]; omega
    have hti : t ≤ i := min_le_left _ _
    have htop : i+1<t+h := by dsimp [t]; omega
    exact (hL t hj').2.2.1 i hti htop

lemma local_of_global {α : Type} [LT α] {r : ℕ→α} {h j t : ℕ}
    (hG : GlobalRows r h j) (ht : t<j) : LocalRows r h t :=
  ⟨fun i _ hi => hG.1 i (by omega) (by omega),
   fun i _ hi => hG.2.1 i (by omega) (by omega),
   fun i _ hi => hG.2.2.1 i (by omega) (by omega),
   hG.2.2.2 t ht⟩

def readRank {n : ℕ} (p : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if hi : i<n then (p ⟨i,hi⟩).val else 0

lemma readRank_fin {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    readRank p i.val=(p i).val := by simp [readRank,i.isLt]

lemma window_fits_iff {h j : ℕ} (hh : 2≤h)
    (p : Equiv.Perm (Fin (nVerts (3*h+1) 3 j))) :
    Packs (delayed h hh) 3 j p ↔ ∀ t, t < j → FitsNat (readRank p) h t := by
  have hE (t : Fin j) (x : Fin (3*h+1)) :
      readRank p (3*t.val+x.val)=(p (window t x)).val := by
    rw [show 3*t.val+x.val = (window (step:=3) t x).val by simp [window]; omega]
    exact readRank_fin p _
  constructor
  · intro hp t ht x y hx hy
    let t' : Fin j := ⟨t,ht⟩
    let x' : Fin (3*h+1) := ⟨x,hx⟩
    let y' : Fin (3*h+1) := ⟨y,hy⟩
    rw [hE t' x',hE t' y']
    exact hp t' x' y'
  · intro hp t x y
    have he := hp t.val t.isLt x.val y.val x.isLt y.isLt
    rwa [hE t x,hE t y] at he

theorem packs_iff_global {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (nVerts (3*h+1) 3 j))) :
    Packs (delayed h hh) 3 j p ↔ GlobalRows (readRank p) h j := by
  rw [window_fits_iff hh]
  constructor
  · intro hp
    exact global_of_local hj hh (fun t ht => local_of_fits hh (hp t ht))
  · intro hG t ht
    exact fits_of_local hh (local_of_global hG ht)

#print axioms packs_iff_global
end CoverCutoff
