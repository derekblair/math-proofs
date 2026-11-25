import DelayLocal

namespace CoverCutoff

def FitsNat {α : Type} [LT α] (r : ℕ→α) (h t : ℕ) : Prop :=
  ∀ x y : ℕ, x < 3*h+1 → y < 3*h+1 →
    (r (3*t+x) < r (3*t+y) ↔ familyRank h x < familyRank h y)

lemma inv_familyRank {h x : ℕ} (hh : 2≤h) (hx : x<3*h+1) :
    invRank h (familyRank h x)=x := by
  have hq := familyRank_bound hh hx
  exact familyRank_inj hh (invRank_bound hh hq) hx (invRank_spec hh hq)

lemma fits_of_local {α : Type} [LinearOrder α] {r : ℕ→α} {h t : ℕ} (hh : 2≤h)
    (hrows : LocalRows r h t) : FitsNat r h t := by
  have hchain : Ascending (fun q => r (3*t+invRank h q)) 0 (3*h+1) :=
    fun q _ hq => row_chain_one hh hrows q (by omega)
  intro x y hx hy
  have hxv := familyRank_bound hh hx
  have hyv := familyRank_bound hh hy
  have imp (a b : ℕ) (ha : a < 3*h+1) (hb : b < 3*h+1)
      (hab : familyRank h a < familyRank h b) : r (3*t+a) < r (3*t+b) := by
    have hres := asc_lt hchain (Nat.zero_le _) (by have := familyRank_bound hh hb; omega) hab
    rwa [inv_familyRank hh ha,inv_familyRank hh hb] at hres
  refine ⟨fun hlt => ?_,imp x y hx hy⟩
  by_contra! hn
  rcases lt_or_eq_of_le hn with hlt'|heq
  · exact (not_lt_of_ge (imp y x hy hx hlt').le) hlt
  · have he := familyRank_inj hh hx hy heq.symm
    exact (lt_irrefl _) (he ▸ hlt)

lemma local_of_fits {α : Type} [LT α] {r : ℕ→α} {h t : ℕ} (hh : 2≤h)
    (hfit : FitsNat r h t) : LocalRows r h t := by
  have HP_A (n : ℕ) : 3*t+posA n=posA (t+n) := by simp [posA]; omega
  have HP_B (n : ℕ) : 3*t+posB n=posB (t+n) := by simp [posB]; omega
  have HP_C (n : ℕ) : 3*t+posC n=posC (t+n) := by simp [posC]; omega
  have ha0 : familyRank h (posA 0)=h-1 := familyRank_A0
  have ha (n : ℕ) (hn : 0<n) : familyRank h (posA n)=h+n := familyRank_A hn
  have hb (n : ℕ) : familyRank h (posB n)=(if n=h-1 then h else n) := familyRank_B
  have hc (n : ℕ) : familyRank h (posC n)=2*h+1+n := familyRank_C
  have PA (n : ℕ) (hn : n≤h) : posA n<3*h+1 := by simp [posA]; omega
  have PB (n : ℕ) (hn : n<h) : posB n<3*h+1 := by simp [posB]; omega
  have PC (n : ℕ) (hn : n<h) : posC n<3*h+1 := by simp [posC]; omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi hi'
    let q := i-t
    have hq : q+1≤h := by dsimp [q]; omega
    have heq : t+q=i := by dsimp [q]; omega
    have heq' : t+(q+1)=i+1 := by omega
    have he := (hfit (posA q) (posA (q+1)) (PA _ (by omega)) (PA _ hq)).mpr
      (by rw [ha (q+1) (by omega)]
          by_cases h0 : q=0
          · rw [h0,ha0]; omega
          · rw [ha q (by omega)]; omega)
    simpa only [HP_A,heq,heq',localA] using he
  · intro i hi hi'
    let q := i-t
    have hq : q+1<h := by dsimp [q]; omega
    have heq : t+q=i := by dsimp [q]; omega
    have heq' : t+(q+1)=i+1 := by omega
    have he := (hfit (posB q) (posB (q+1)) (PB _ (by omega)) (PB _ hq)).mpr
      (by rw [hb,hb]; split_ifs <;> omega)
    simpa only [HP_B,heq,heq',localB] using he
  · intro i hi hi'
    let q := i-t
    have hq : q+1<h := by dsimp [q]; omega
    have heq : t+q=i := by dsimp [q]; omega
    have heq' : t+(q+1)=i+1 := by omega
    have he := (hfit (posC q) (posC (q+1)) (PC _ (by omega)) (PC _ hq)).mpr
      (by rw [hc,hc]; omega)
    simpa only [HP_C,heq,heq',localC] using he
  · have he := (hfit (posB (h-2)) (posA 0) (PB _ (by omega)) (PA _ (by omega))).mpr
      (by rw [hb,ha0]; split_ifs <;> omega)
    simpa only [HP_A,HP_B,Nat.add_zero,show t+(h-2)=t+h-2 by omega,localA,localB] using he
  · have he := (hfit (posA 0) (posB (h-1)) (PA _ (by omega)) (PB _ (by omega))).mpr
      (by rw [ha0,hb,if_pos rfl]; omega)
    simpa only [HP_A,HP_B,Nat.add_zero,show t+(h-1)=t+h-1 by omega,localA,localB] using he
  · have he := (hfit (posB (h-1)) (posA 1) (PB _ (by omega)) (PA _ (by omega))).mpr
      (by rw [hb,if_pos rfl,ha _ (by decide)]; omega)
    simpa only [HP_A,HP_B,show t+(h-1)=t+h-1 by omega,localA,localB] using he
  · have he := (hfit (posA h) (posC 0) (PA _ le_rfl) (PC _ (by omega))).mpr
      (by rw [ha _ (by omega),hc]; omega)
    simpa only [HP_A,HP_C,Nat.add_zero,localA,localC] using he

theorem local_iff_fits {α : Type} [LinearOrder α] {r : ℕ→α} {h t : ℕ} (hh : 2≤h) :
    LocalRows r h t ↔ FitsNat r h t := ⟨fits_of_local hh,local_of_fits hh⟩

#print axioms local_iff_fits
end CoverCutoff
