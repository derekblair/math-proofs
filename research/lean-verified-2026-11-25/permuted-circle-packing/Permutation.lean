import Packing

namespace PermCircles

lemma order_pos {m b : ℤ} (hm : 1 ≤ m) (hb : m+1 ≤ b) : 0 < order m b := by
  unfold order
  nlinarith [mul_nonneg (show 0 ≤ m by omega) (show 0 ≤ b-1 by omega)]

lemma order_cast {m b : ℤ} (h : 0 < order m b) :
    (Int.toNat (order m b) : ℤ) = order m b :=
  Int.toNat_of_nonneg (le_of_lt h)

def target (m b x : ℤ) : ℤ := (slope b*x) % order m b

lemma target_characteristic (m b x : ℤ) :
    (2*m+1)*target m b x-x = order m b*(-2*x-(2*m+1)*(slope b*x/order m b)) := by
  have h := Int.emod_add_mul_ediv (slope b*x) (order m b)
  change target m b x + order m b * (slope b*x / order m b) = slope b*x at h
  calc
    (2*m+1) * target m b x - x =
        (2*m+1) * (slope b*x) - x - (2*m+1)*order m b*(slope b*x/order m b) := by
      linear_combination (2*m+1)*h
    _ = _ := by
      rw [← mul_assoc,inverse_slope]
      ring

lemma target_mod_inverse (m b x : ℤ) :
    ((2*m+1)*target m b x) % order m b = x % order m b := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(-2*x-(2*m+1)*(slope b*x/order m b)),?_⟩
  linear_combination -target_characteristic m b x

lemma target_fin {m b : ℤ} (h : 0 < order m b) (x : Fin (order m b).toNat) :
    (target m b x.val).toNat < (order m b).toNat := by
  have h0 : 0 ≤ target m b x.val := Int.emod_nonneg _ (ne_of_gt h)
  have h' : target m b x.val < order m b := Int.emod_lt_of_pos _ h
  exact (Int.toNat_lt_toNat h).mpr h'

noncomputable def modular (m b : ℤ) (h : 0 < order m b) : Equiv.Perm (Fin (order m b).toNat) :=
  Equiv.ofBijective (fun x => ⟨(target m b x.val).toNat,target_fin h x⟩) <|
    Finite.injective_iff_bijective.mp (by
      intro x y hxy
      have ha : 0 ≤ target m b x.val := Int.emod_nonneg _ (ne_of_gt h)
      have hb : 0 ≤ target m b y.val := Int.emod_nonneg _ (ne_of_gt h)
      have he := congrArg Fin.val hxy
      change (target m b x.val).toNat = (target m b y.val).toNat at he
      have he' := congrArg (fun t : ℕ => (t : ℤ)) he
      rw [Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hb] at he'
      have hix : (x.val:ℤ) < ((order m b).toNat:ℤ) := by exact_mod_cast x.isLt
      have hiy : (y.val:ℤ) < ((order m b).toNat:ℤ) := by exact_mod_cast y.isLt
      rw [order_cast h] at hix hiy
      have hmx : (x.val : ℤ) % order m b = x.val := Int.emod_eq_of_lt (by positivity) hix
      have hmy : (y.val : ℤ) % order m b = y.val := Int.emod_eq_of_lt (by positivity) hiy
      have ht := target_mod_inverse m b x.val
      rw [he',target_mod_inverse,hmx,hmy] at ht
      apply Fin.ext
      exact_mod_cast ht.symm)

lemma modular_val (m b : ℤ) (h : 0 < order m b) (x : Fin (order m b).toNat) :
    ((modular m b h x).val : ℤ) = target m b x.val := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt h))

lemma modular_distance {m b : ℤ} (hm : 1 ≤ m) (hb : m+1 ≤ b)
    (hbq : 3*m^2 ≤ (b-1)^2) (i j : Fin (order m b).toNat) (hij : i ≠ j) :
    (2*m)^2 ≤ ((i.val : ℤ)-j.val)^2 +
      (((modular m b (order_pos hm hb) i).val : ℤ)-(modular m b (order_pos hm hb) j).val)^2 := by
  rw [modular_val,modular_val]
  let x := (i.val : ℤ)-j.val
  let y := target m b i.val - target m b j.val
  let c := (-2*(i.val : ℤ)-(2*m+1)*(slope b*i.val/order m b)) -
           (-2*(j.val : ℤ)-(2*m+1)*(slope b*j.val/order m b))
  let a := y-b*c
  have hc : (2*m+1)*y-x = order m b*c := by
    dsimp [x,y,c]
    linear_combination target_characteristic m b i.val - target_characteristic m b j.val
  have hy : a+b*c = y := by dsimp [a]; ring
  have hx : (2*m+1)*a+m*c = x := by
    dsimp [a]
    unfold order at hc
    linear_combination hc
  have hn : a ≠ 0 ∨ c ≠ 0 := by
    by_contra! hf
    rw [hf.1,hf.2] at hx
    simp [x] at hx
    exact hij (Fin.ext (by omega))
  have h := euclidean_lower hm hb hbq hn
  rw [hx,hy] at h
  exact h

#print axioms modular_distance
end PermCircles
