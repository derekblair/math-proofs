import Mathproofs.ESDescentTransfer
import Mathproofs.ESCovering

/-!
# From branch-2 descent arithmetic to positive covering identities

This module supplies a precise arithmetic-to-identity bridge independently of
any external branch census. For n = 4Xt+s and x = Xt+x₀, the conditions

* 4x₀ = s+m;
* mAr ∣ X(A+r) (the slope/key condition);
* mAr ∣ x₀(A+r) (the constant/S3 condition)

construct a positive natural linear factor C and denominators x, nAC, nrC.
Their rational identity is proved, not assumed.

`transfer_00_covering` composes the existing (0,0) key transfer with an
intercept shift x₀′ = X₀j+x₀, deriving the parent S3 condition by subtraction.
`transfer_11_covering` cancels q from both the slope and intercept when
A=qA₀, r=qr₀, X′=qX₀, and x₀′=qx₀ are supplied explicitly.

These are conditional coverage results for the stated positive parameters.
They do not prove that every external branch-2 identity has the required
normalization, supply the absent R74 target sweep, or certify its contradiction.
-/

namespace ESDescentCovering

/-- The branch-2 denominator algebra. The factor equation determines C from
raw integer parameters; no rational Egyptian-fraction identity is a premise. -/
theorem branch2_pointwise (n x m A r C : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hA : 0 < A) (hr : 0 < r) (hC : 0 < C)
    (hfirst : 4*x = n+m) (hfactor : m*(A*r)*C = x*(A+r)) :
    ESCovering.Covered n := by
  apply ESCovering.of_cross_product n x (n*A*C) (n*r*C) hn hx
    (by positivity) (by positivity)
  calc
    4*x*(n*A*C)*(n*r*C) = (n+m)*n^2*A*r*C^2 := by rw [← hfirst]; ring
    _ = n*((n*A*C)*(n*r*C)) + n^2*C*(m*(A*r)*C) := by ring
    _ = n*((n*A*C)*(n*r*C)) + n^2*C*(x*(A+r)) := by rw [hfactor]
    _ = n*((n*A*C)*(n*r*C)+x*(n*r*C)+x*(n*A*C)) := by ring

/-- Integral slope and intercept produce a covering identity on the entire
progression, including t=0, with positive natural denominators. -/
theorem branch2_covering_of_divisibility (X s m A r x₀ : ℕ)
    (hs : 0 < s) (hm : 0 < m) (hA : 0 < A) (hr : 0 < r)
    (hfirst : 4*x₀ = s+m)
    (hkey : m*(A*r) ∣ X*(A+r))
    (hS3 : m*(A*r) ∣ x₀*(A+r)) :
    ESCovering.CoversClass (4*X) s := by
  obtain ⟨P, hP⟩ := hkey
  obtain ⟨c, hc⟩ := hS3
  have hx₀ : 0 < x₀ := by omega
  have hcpos : 0 < c := by
    have hpos : 0 < x₀*(A+r) := Nat.mul_pos hx₀ (by omega)
    by_contra h
    have : c = 0 := by omega
    simp [this] at hc
    omega
  intro t
  apply branch2_pointwise ((4*X)*t+s) (X*t+x₀) m A r (P*t+c)
    (by omega) (by omega) hA hr (by omega)
  · calc
      4*(X*t+x₀) = (4*X)*t + 4*x₀ := by ring
      _ = (4*X)*t+s+m := by rw [hfirst]; omega
  · calc
      m*(A*r)*(P*t+c) = (m*(A*r)*P)*t + m*(A*r)*c := by ring
      _ = (X*(A+r))*t + x₀*(A+r) := by rw [← hP, ← hc]
      _ = (X*t+x₀)*(A+r) := by ring

/-- Once the slope divisibility is known, an integral shifted intercept
implies an integral parent intercept. -/
theorem descend_intercept {D X A r x₀' x₀ j : ℕ}
    (hkey : D ∣ X*(A+r)) (hS3 : D ∣ x₀'*(A+r))
    (hshift : x₀' = X*j+x₀) : D ∣ x₀*(A+r) := by
  have hshiftD : D ∣ (X*(A+r))*j := dvd_mul_of_dvd_left hkey j
  have hsum : D ∣ (X*(A+r))*j + x₀*(A+r) := by
    convert hS3 using 1
    rw [hshift]
    ring
  exact (Nat.dvd_add_iff_right hshiftD).mpr hsum

/-- A genuine (0,0) arithmetic-to-identity descent. The refined S3 intercept
is shifted to the parent using the descended key, then positive denominators
are constructed for every member of the parent progression. -/
theorem transfer_00_covering
    {q μ m m₀ d₀ A' B' A r X' X₀ x₀' x₀ s j : ℕ}
    (hq : q.Prime)
    (hA : A = d₀*A') (hr : r = d₀*B') (hm : m = q^μ*m₀)
    (hAq : ¬ q ∣ A) (hrq : ¬ q ∣ r) (hmq : ¬ q ∣ m₀)
    (hX : X' = q*X₀) (hμ : q^μ ∣ A'+B')
    (hkey : m*(A*r) ∣ X'*(A+r))
    (hS3 : m*(A*r) ∣ x₀'*(A+r))
    (hshift : x₀' = X₀*j+x₀)
    (hs : 0 < s) (hmpos : 0 < m) (hApos : 0 < A) (hrpos : 0 < r)
    (hfirst : 4*x₀ = s+m) :
    ESCovering.CoversClass (4*X₀) s := by
  have hk := ESDescentTransfer.transfer_key_00 hq hA hr hm hAq hrq hmq hX hμ hkey
  exact branch2_covering_of_divisibility X₀ s m A r x₀ hs hmpos hApos hrpos hfirst
    hk (descend_intercept hk hS3 hshift)

/-- A genuine (1,1) arithmetic-to-identity descent with an explicitly scaled
intercept. Both slope and S3 divisibilities follow by exact q-cancellation. -/
theorem transfer_11_covering {q m A₀ r₀ A r X' X₀ x₀' x₀ s : ℕ}
    (hq : 0 < q) (hA : A = q*A₀) (hr : r = q*r₀)
    (hX : X' = q*X₀) (hx : x₀' = q*x₀)
    (hkey : m*(A*r) ∣ X'*(A+r))
    (hS3 : m*(A*r) ∣ x₀'*(A+r))
    (hs : 0 < s) (hm : 0 < m) (hApos : 0 < A₀) (hrpos : 0 < r₀)
    (hfirst : 4*x₀ = s+m) :
    ESCovering.CoversClass (4*X₀) s := by
  have hk := (ESDescentTransfer.transfer_qcancel hq hA hr hX).mpr hkey
  have hc := (ESDescentTransfer.transfer_qcancel hq hA hr hx).mpr hS3
  exact branch2_covering_of_divisibility X₀ s m A₀ r₀ x₀ hs hm hApos hrpos hfirst hk hc

end ESDescentCovering
