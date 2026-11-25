import NonconvData
namespace Nonconv

def Matches (f : Nat → Nat) (s : Nat) (k : Fin 44) : Prop :=
  ∀ i < 9, ∀ j < 9, (f (s+i) > f (s+j)) ↔ (word k i > word k j)

theorem actualKeys (f : Nat → Nat) (s : Nat) (u v : Fin 44)
    (hu : Matches f s u) (hv : Matches f (s+1) v) :
    (row u).suffixKey = (row v).prefixKey := by
  rw [←(exactKeys u).2,←(exactKeys v).1]
  unfold invKey
  congr 2
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro j hj
  have ha := List.mem_range.mp hi
  have hb := List.mem_range.mp (List.mem_of_mem_filter hj)
  simp only [zero_add]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have h1 := hu (1+i) (by omega) (1+j) (by omega)
  have h2 := hv i (by omega) j (by omega)
  rw [show s+(1+i)=s+1+i by omega,show s+(1+j)=s+1+j by omega] at h1
  exact h1.symm.trans h2

theorem overlap_real (f : Nat → Nat) (s : Nat) (u v : Fin 44)
    (hu : Matches f s u) (hv : Matches f (s+1) v) :
    (row u).lane = (row v).lane ∧ ((row u).phase+1)%3 = (row v).phase :=
  overlapTags u v (actualKeys f s u v hu hv)

theorem steady (f : Nat → Nat) (m : Nat) (u : Nat → Fin 44)
    (h : ∀ i<m, Matches f i (u i)) (i : Nat) (hi : i<m) :
    (row (u i)).lane = (row (u 0)).lane ∧ (row (u i)).phase = ((row (u 0)).phase+i)%3 := by
  induction i with
  | zero =>
    constructor
    · rfl
    · have hh := (labelBounds (u 0)).2
      simpa using (Nat.mod_eq_of_lt hh).symm
  | succ i ih =>
    obtain ⟨h1,h2⟩ := ih (by omega)
    obtain ⟨e1,e2⟩ := overlap_real f i (u i) (u (i+1)) (h i (by omega)) (h (i+1) hi)
    constructor
    · omega
    · rw [h2] at e2
      omega

def block (o i : Nat) : Nat := (o+i)/3

set_option maxHeartbeats 8000000 in
theorem rowCross : ∀ (k : Fin 44) (i j : Fin 9),
    block (row k).phase i.val < block (row k).phase j.val →
    if (row k).lane=0 then word k i.val < word k j.val else word k j.val < word k i.val := by
  decide

theorem nearCross (f : Nat → Nat) (n : Nat) (hn : 9 ≤ n) (u : Nat → Fin 44)
    (h : ∀ i<n-8, Matches f i (u i)) (i j : Nat) (hj : j<n) (hij : i ≤ j ∧ j ≤ i + 8)
    (hc : block (row (u 0)).phase i < block (row (u 0)).phase j) :
    if (row (u 0)).lane=0 then f i < f j else f j < f i := by
  let s := min i (n-9)
  have h1 : s ≤ i ∧ s ≤ j ∧ j < s + 9 ∧ s + 8 < n := by
    simp only [s,Nat.min_def]
    split <;> omega
  have hs := steady f (n-8) u h s (by omega)
  have hp := hs.2
  let a : Fin 9 := ⟨i-s, by omega⟩
  let b : Fin 9 := ⟨j-s, by omega⟩
  have hb : block (row (u s)).phase a.val < block (row (u s)).phase b.val := by
    rw [hp]
    dsimp [block,a,b] at *
    omega
  have hh := rowCross (u s) a b hb
  rw [hs.1] at hh
  have he₁ : s+a.val=i := by dsimp [a]; omega
  have he₂ : s+b.val=j := by dsimp [b]; omega
  have ha : a.val<9 := a.isLt
  have hb' : b.val<9 := b.isLt
  by_cases hz : (row (u 0)).lane=0
  · simp only [if_pos hz] at hh ⊢
    have hcmp := (h s (by omega)) b.val hb' a.val ha
    rw [he₂,he₁] at hcmp
    exact hcmp.mpr hh
  · simp only [if_neg hz] at hh ⊢
    have hcmp := (h s (by omega)) a.val ha b.val hb'
    rw [he₁,he₂] at hcmp
    exact hcmp.mpr hh

theorem allCross (f : Nat → Nat) (n : Nat) (hn : 9 ≤ n) (u : Nat → Fin 44)
    (h : ∀ i<n-8, Matches f i (u i)) (i j : Nat) (hj : j<n)
    (hc : block (row (u 0)).phase i < block (row (u 0)).phase j) :
    if (row (u 0)).lane=0 then f i < f j else f j < f i := by
  have hij : i≤j := by unfold block at hc; omega
  have hh (d : Nat) : ∀ k, k + d < n →
      block (row (u 0)).phase k < block (row (u 0)).phase (k+d) →
      if (row (u 0)).lane=0 then f k < f (k+d) else f (k+d) < f k := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro k hk hx
      by_cases hb : d ≤ 8
      · exact nearCross f n hn u h k (k+d) hk (by omega) hx
      · have hleft : block (row (u 0)).phase k < block (row (u 0)).phase (k+3) := by
          unfold block
          omega
        have hright : block (row (u 0)).phase (k+3) < block (row (u 0)).phase ((k+3)+(d-3)) := by
          unfold block
          omega
        have r1 := nearCross f n hn u h k (k+3) (by omega) (by omega) hleft
        have r2 := ih (d-3) (by omega) (k+3) (by omega) hright
        rw [show k+3+(d-3)=k+d by omega] at r2
        split_ifs at r1 r2 ⊢ <;> omega
  have hx := hh (j-i) i (by omega) (by rwa [show i+(j-i)=j by omega])
  rwa [show i+(j-i)=j by omega] at hx

end Nonconv
