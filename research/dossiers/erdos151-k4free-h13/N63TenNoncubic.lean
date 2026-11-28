import N63FiveComplete
import N63TenNormalize

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

theorem blocks_ten_witness (w : V) (d q : Nat) (hq : d+q=9) (hd : 4≤d)
    (L : Fin d ≃ {z : V // G w z}) (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z})
    (f : Fin d → Fin (2^q)) (fm : ∀ i j : Fin d, i.val≤j.val → (f i).val≤(f j).val)
    (hbits : ∀ (i : Fin d) (j : Fin q), (f i).val.testBit j.val = decide (G (L i).val (R j).val))
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (hL : ∀ i j, ¬G (L i).val (L j).val)
    (hD : fullDeg G w=d) (hmin : ∀ v, 2≤fullDeg G v) (hmax : ∀ v, fullDeg G v≤d)
    (dense : 30≤∑ v : V,fullDeg G v) : TenWitness G := by
  have bal := right_degree_balance G w L R sym (irr w) hL hD
  have hd8 : d≤8 := by
    by_contra! h
    have hq0 : q=0 := by omega
    subst q
    simp at bal
    omega
  by_cases hd5 : d=5
  · cases hd5
    have hq4 : q=4 := by omega
    subst q
    exact five_blocks_witness G w L R f fm hbits sym irr tf hL hD hmin hmax dense
  · let rd := rightDeg G (fun j => (R j).val)
    let deg := fun j => fullDeg G (R j).val
    obtain ⟨j,hj,hk⟩ := fixed_pivot_except_five d q hq hd hd8 hd5 deg rd
      (fun j => ⟨hmin _,hmax _⟩) (fun j => rightDeg_lt G _ irr j) (by
        change 30 + (∑ j, rightDeg G (fun j => (R j).val) j) ≤ 2*d+2*∑ j,fullDeg G (R j).val
        omega)
    obtain ⟨S,hS,hSz,hI⟩ := rightPool_witness G (by omega) (fun j => (R j).val) j irr sym tf
    apply witness_right_pool G w R j S hS hI
    rw [hD]
    exact minCenter_sound _ _ _ hd8 ((hmax _).trans hd8) hj (hk.trans hSz)

/-- Every triangle-free ten-link with minimum degree two, at least 15 edges,
and a vertex of degree at least four admits the three-hub insertion pivot. -/
theorem noncubic_ten_witness (hn : Fintype.card V=10)
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (hmin : ∀ v, 2≤fullDeg G v)
    (dense : 30≤∑ v : V,fullDeg G v)
    (high : ∃ v, 4≤fullDeg G v) : TenWitness G := by
  obtain ⟨w,hw,hwn,hm,L,R,M,hmono,hwid,hbits,hL,_⟩ :=
    max_normalization_sorted_of_high G 10 hn high irr tf
  let q := 9-fullDeg G w
  let f (i : Fin (fullDeg G w)) : Fin (2^q) := ⟨M i,hwid i⟩
  apply blocks_ten_witness G w (fullDeg G w) q (by change _+ (9-_) = 9; omega) hw L R f
    (fun i j h => hmono h) _ sym irr tf hL rfl hmin hm dense
  intro i j
  apply Bool.eq_iff_iff.mpr
  simpa [f] using hbits i j

#print axioms noncubic_ten_witness

theorem cubic_of_no_ten_witness (hn : Fintype.card V=10)
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (hmin : ∀ v, 2≤fullDeg G v) (dense : 30≤∑ v : V,fullDeg G v)
    (no : ¬TenWitness G) :
    ∀ v, fullDeg G v=3 := by
  have H (v : V) : fullDeg G v≤3 := by
    by_contra! h
    exact no (noncubic_ten_witness G hn sym irr tf hmin dense ⟨v,h⟩)
  intro v
  by_contra! h
  have lt : fullDeg G v < 3 := by have := H v; omega
  have ht : (∑ i : V, fullDeg G i) < ∑ _i : V, (3:Nat) :=
    Finset.sum_lt_sum (fun i _ => H i) ⟨v,Finset.mem_univ _,lt⟩
  simp [hn] at ht
  omega

#print axioms cubic_of_no_ten_witness
end Erdos151N63
