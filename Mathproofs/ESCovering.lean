import Mathproofs.WitnessComplexThm13

/-!
# Constructive Erdős–Straus covering bridges

`Covered n` includes positive natural denominators and the rational identity.
The splitting bridge derives those witnesses from divisibility and the two
elementary parameter equations; it never assumes the desired identity.
-/

namespace ESCovering

def Covered (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / n = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

def CoversClass (M s : ℕ) : Prop := ∀ t : ℕ, Covered (M * t + s)

/-- Clear the denominators of a positive natural Egyptian-fraction identity. -/
theorem of_cross_product (n x y z : ℕ) (hn : 0 < n) (hx : 0 < x)
    (hy : 0 < y) (hz : 0 < z)
    (heq : 4*x*y*z = n*(y*z+x*z+x*y)) : Covered n := by
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hy
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hz
  have heqq : (4 : ℚ)*x*y*z = n*(y*z+x*z+x*y) := by exact_mod_cast heq
  field_simp
  nlinarith [heqq]

/-- The splitting construction, with the quotient witnesses proved positive. -/
theorem of_split (n x m h a b : ℕ) (hn : 0 < n) (hx : 0 < x)
    (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (hfirst : 4*x = n+m) (hsum : a+b = m*h)
    (hdiv : a*b ∣ x*h) : Covered n := by
  obtain ⟨u, hu⟩ := dvd_trans (dvd_mul_right a b) hdiv
  obtain ⟨v, hv⟩ := dvd_trans (dvd_mul_left b a) hdiv
  have hu0 : 0 < u := by nlinarith [Nat.mul_pos hx hh]
  have hv0 : 0 < v := by nlinarith [Nat.mul_pos hx hh]
  apply of_cross_product n x (n*u) (n*v) hn hx (by positivity) (by positivity)
  have he : h*(4*x*(n*u)*(n*v)) = h*(n*((n*u)*(n*v)+x*(n*v)+x*(n*u))) := by
    calc
      h*(4*x*(n*u)*(n*v)) = (n+m)*h*n^2*u*v := by rw [← hfirst]; ring
      _ = n*h*n^2*u*v + (a+b)*n^2*u*v := by rw [hsum]; ring
      _ = n*h*n^2*u*v + n^2*v*(a*u) + n^2*u*(b*v) := by ring
      _ = h*(n*((n*u)*(n*v)+x*(n*v)+x*(n*u))) := by
        rw [← hu, ← hv]
        ring
  exact Nat.eq_of_mul_eq_mul_left hh he

/-- R38's progression premise yields positive integral covering witnesses for
every nonnegative parameter, including the first member of the progression. -/
theorem splitting_family (k₀ c h a b : ℕ) (hc : 0 < c) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b)
    (hsum : a+b = (4*c-1)*h)
    (hdiv : a*b ∣ h * Nat.gcd 2310 (6*k₀+c)) :
    CoversClass 9240 (24*k₀+1) := by
  intro t
  apply of_split (9240*t+(24*k₀+1)) (2310*t+(6*k₀+c)) (4*c-1) h a b
    (by omega) (by omega) hh ha hb
  · omega
  · exact hsum
  · have hd₁ : a*b ∣ h*2310 := dvd_trans hdiv (Nat.mul_dvd_mul_left h (Nat.gcd_dvd_left _ _))
    have hd₂ : a*b ∣ h*(6*k₀+c) := dvd_trans hdiv (Nat.mul_dvd_mul_left h (Nat.gcd_dvd_right _ _))
    convert Nat.dvd_add (dvd_mul_of_dvd_left hd₁ t) hd₂ using 1
    ring

/-- Construct the positive T2 quotient from its divisibility condition, then
apply the existing full-class identity. -/
theorem of_t2 (a c d n q : ℕ) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hn : 0 < n) (hq : q+1 = 4*a*c*d) (hdiv : q ∣ c*n+a) : Covered n := by
  obtain ⟨m, hm⟩ := hdiv
  have hmpos : 0 < m := by nlinarith
  refine ⟨a*d*m, n*a*c*d, n*c*d*m, by positivity, by positivity, by positivity, ?_⟩
  simpa only [Nat.cast_mul] using WitnessComplexThm13.t3_full_class a c d n m q
    ha hc hd hn hmpos hq hm.symm

end ESCovering
