import Std
namespace Emerging
abbrev Word := Fin 5 → Nat
def w (k : Fin 7) : Word :=
  fun i => ([[1,2,3,4,5], [1,2,4,5,3], [2,4,5,3,1], [4,5,3,2,1],
    [5,4,3,2,1], [2,1,4,3,5], [1,3,2,5,4]][k.val]!)[i.val]!
def testOverlap (u v : Fin 7) : Bool :=
 (List.finRange 4).all fun i => (List.finRange 4).all fun j =>
   decide ((w u ⟨i+1,by omega⟩ < w u ⟨j+1,by omega⟩) ↔
      (w v ⟨i,by omega⟩ < w v ⟨j,by omega⟩))
def allowedEdges (u v : Fin 7) : Prop :=
 (u.val = 0 ∧ (v.val = 0 ∨ v.val = 1)) ∨ (u.val = 1 ∧ v.val = 2) ∨
 (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 4) ∨
 (u.val = 4 ∧ v.val = 4) ∨ (u.val = 5 ∧ v.val = 6) ∨ (u.val = 6 ∧ v.val = 5)
theorem overlapTable :
  ∀ u v : Fin 7, testOverlap u v = true → allowedEdges u v := by
  unfold allowedEdges
  decide
def matchWord (f : Nat → Nat) (i : Nat) (a : Word) :=
  ∀ r s : Fin 5, f (i+r.val) < f (i+s.val) ↔ a r < a s
theorem step (f : Nat → Nat) (i : Nat) (u v : Fin 7)
  (hu : matchWord f i (w u)) (hv : matchWord f (i+1) (w v)) :
  allowedEdges u v := by
  apply overlapTable
  unfold testOverlap
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  intro r s
  have a := hu ⟨r.val+1,by omega⟩ ⟨s.val+1,by omega⟩
  have b := hv ⟨r.val,by omega⟩ ⟨s.val,by omega⟩
  have ar : i+(r.val+1) = i+1+r.val := by omega
  have as : i+(s.val+1) = i+1+s.val := by omega
  simp only at a b
  rw [ar,as] at a
  exact a.symm.trans b
def Path (u : Nat → Fin 7) (m : Nat) : Prop :=
  ∀ i, i+1 < m → allowedEdges (u i) (u (i+1))

theorem path_alt_iff (u : Nat → Fin 7) (m : Nat) (h : Path u m) (i : Nat) (hi : i < m) :
    5 ≤ (u i).val ↔ 5 ≤ (u 0).val := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have he := h i (by omega)
    unfold allowedEdges at he
    exact (show 5 ≤ (u (i+1)).val ↔ 5 ≤ (u i).val by omega).trans (ih (by omega))

theorem path_after_peak (u : Nat → Fin 7) (m i d : Nat) (h : Path u m)
    (hi : (u i).val = 2) (hb : i+d+1 < m) :
    3 ≤ (u (i+d+1)).val ∧ (u (i+d+1)).val ≤ 4 := by
  induction d with
  | zero =>
    have he := h i (by omega)
    unfold allowedEdges at he
    simpa using (show 3 ≤ (u (i+1)).val ∧ (u (i+1)).val ≤ 4 by omega)
  | succ d ih =>
    have ih' := ih (by omega)
    have he := h (i+d+1) (by omega)
    unfold allowedEdges at he
    rw [show i+(d+1)+1 = i+d+1+1 by omega]
    omega

theorem path_unique_peak (u : Nat → Fin 7) (m a b : Nat) (h : Path u m)
    (hab : a < b) (hb : b < m) (ha : (u a).val = 2) :
    (u b).val ≠ 2 := by
  let d := b-a-1
  have hd : a+d+1 = b := by dsimp [d]; omega
  have hh := path_after_peak u m a d h ha (by omega)
  rw [hd] at hh
  omega

theorem B_edge_peak_start_last (u : Nat → Fin 7) (m i : Nat) (h : Path u m)
    (hn : ∀ j < m, (u j).val ≠ 2) (hi : i < m) :
    ((u i).val = 1 → i+1=m) ∧ ((u i).val = 3 → i=0) := by
  constructor
  · intro hp
    by_cases hn' : i+1=m
    · exact hn'
    · exfalso
      have hb : i+1<m := by omega
      have he := h i hb
      unfold allowedEdges at he
      have hz := hn (i+1) hb
      omega
  · intro hp
    by_cases hn' : i=0
    · exact hn'
    · exfalso
      have he := h (i-1) (by omega)
      have hz := hn (i-1) (by omega)
      rw [show i-1+1=i by omega] at he
      unfold allowedEdges at he
      omega

/-- If two bounded permutations have the same local windows and one has a
short-step inverse rank path, its local comparisons uniquely determine the other. -/
theorem compare_near (f g : Nat → Nat) (n : Nat) (hn : 5 ≤ n) (a b : Nat)
    (ha : a < n) (hb : b < n) (hab : a ≤ b+4 ∧ b ≤ a+4)
    (hw : ∀ j, j+4<n → ∃ u : Fin 7, matchWord f j (w u) ∧ matchWord g j (w u)) :
    f a < f b ↔ g a < g b := by
  let j := min (min a b) (n-5)
  have h1 : j≤a ∧ j≤b ∧ j+4<n := by
    simp only [j, Nat.min_def]
    split <;> split <;> omega
  have h2 : a-j<5 ∧ b-j<5 := by
    simp only [j, Nat.min_def]
    split <;> split <;> omega
  obtain ⟨u,hf,hg⟩ := hw j h1.2.2
  let i1 : Fin 5 := ⟨a-j,h2.1⟩
  let i2 : Fin 5 := ⟨b-j,h2.2⟩
  have hf' := hf i1 i2
  have hg' := hg i1 i2
  have e1 : j + i1.val = a := by dsimp [i1]; omega
  have e2 : j + i2.val = b := by dsimp [i2]; omega
  rw [e1,e2] at hf' hg'
  exact hf'.trans hg'.symm

theorem strict_gap (f : Nat → Nat) (n : Nat)
    (hs : ∀ i, i+1<n → f i < f (i+1)) (a b : Nat)
    (hab : a≤b) (hb : b<n) : f a + (b-a) ≤ f b := by
  induction b with
  | zero =>
    have : a=0 := by omega
    subst a
    simp
  | succ b ih =>
    by_cases he : a=b+1
    · subst a
      simp
    · have hh := ih (by omega) (by omega)
      have hk := hs b (by omega)
      omega

theorem unique_ranks (f : Nat → Nat) (n : Nat)
    (hs : ∀ i, i+1<n → f i < f (i+1))
    (hb : ∀ i, i<n → f i < n) (i : Nat) (hi : i<n) : f i=i := by
  have hlo := strict_gap f n hs 0 i (by omega) hi
  have hhi := strict_gap f n hs i (n-1) (by omega) (by omega)
  have hx := hb (n-1) (by omega)
  omega

theorem path_from_four (u : Nat → Fin 7) (m i d : Nat) (h : Path u m)
    (hi : (u i).val = 4) (hb : i+d < m) :
    (u (i+d)).val = 4 := by
  induction d with
  | zero => simpa using hi
  | succ d ih =>
    have ih' := ih (by omega)
    have he := h (i+d) (by omega)
    rw [show i+(d+1)=i+d+1 by omega]
    unfold allowedEdges at he
    omega

theorem B_from_zero (u : Nat → Fin 7) (m i : Nat) (h : Path u m)
    (hn : ∀ j < m, (u j).val ≠ 2) (hu : (u 0).val = 0)
    (hi : i+1 < m) : (u i).val = 0 := by
  induction i with
  | zero => exact hu
  | succ i ih =>
    have ih' := ih (by omega)
    have he := h i (by omega)
    have hp := (B_edge_peak_start_last u m (i+1) h hn (by omega)).1
    unfold allowedEdges at he
    omega

theorem path_alt_signature (u : Nat → Fin 7) (m i : Nat) (h : Path u m)
    (hu : 5 ≤ (u 0).val) (hi : i < m) :
    (u i).val = if i % 2 = 0 then (u 0).val else 11 - (u 0).val := by
  induction i with
  | zero => simp
  | succ i ih =>
    have he := h i (by omega)
    have ih' := ih (by omega)
    have hu' := (u 0).isLt
    unfold allowedEdges at he
    split at ih' <;> split <;> omega

#print axioms overlapTable
#print axioms path_unique_peak
end Emerging
