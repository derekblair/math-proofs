import HaarMetaQuotientDispatchCore

namespace HaarMetaPrimitiveCore
open HaarMetaQuotientDispatchCore HaarMetaQuotientGeometry HaarMetaAlgebraCore
open HaarMetaEarlyCases HaarMetaPrimitiveDispatch
variable {G Q : Type*} [Group G] [CommGroup Q]

theorem p013 [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : HaarClass4Generate.Generates x y)
    (h3 : f y=(f x)^3) (big : 10≤orderOf (f x) → Good x y) : Good x y := by
  have eq : A f y=(3:ℤ) • A f x := by
    rw [show (3:ℤ)=(3:ℕ) by rfl, Nat.cast_smul_eq_nsmul]; exact h3
  have hz := mult_span (f x) (primitive_013 _ _ (span_after f onto x y gen) eq)
  apply large_or_affine odd f onto ab x y x hx hy ne gen (0:Fin 3) hz
  · exact (pow_one _).symm
  · exact h3
  · exact big

theorem p014 [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : HaarClass4Generate.Generates x y)
    (h4 : f y=(f x)^4) (big : 12≤orderOf (f x) → Good x y) : Good x y := by
  have eq : A f y=(4:ℤ) • A f x := by
    rw [show (4:ℤ)=(4:ℕ) by rfl, Nat.cast_smul_eq_nsmul]; exact h4
  have hz := mult_span (f x) (primitive_014 _ _ (span_after f onto x y gen) eq)
  apply large_or_affine odd f onto ab x y x hx hy ne gen (1:Fin 3) hz
  · exact (pow_one _).symm
  · exact h4
  · exact big

theorem p025 [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : HaarClass4Generate.Generates x y)
    (h52 : (f x)^5=(f y)^2)
    (big : ∀ z : G, f x=(f z)^2 → f y=(f z)^5 → 13≤orderOf (f z) → Good x y) : Good x y := by
  let z := y*(x^2)⁻¹
  have eq : (5:ℤ) • A f x=(2:ℤ) • A f y := by
    rw [show (5:ℤ)=(5:ℕ) by rfl, show (2:ℤ)=(2:ℕ) by rfl, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h52
  have ez : A f z=A f y-(2:ℤ) • A f x := by
    rw [show (2:ℤ)=(2:ℕ) by rfl,Nat.cast_smul_eq_nsmul]
    rw [sub_eq_add_neg]
    change f z=f y*((f x)^2)⁻¹
    simp [z]
  obtain ⟨px,py,hz⟩ := primitive_025 _ _ (span_after f onto x y gen) eq
  change A f x=(2:ℤ) • (A f y-(2:ℤ) • A f x) at px
  change A f y=(5:ℤ) • (A f y-(2:ℤ) • A f x) at py
  change AddSubgroup.zmultiples (A f y-(2:ℤ) • A f x)=⊤ at hz
  rw [←ez,show (2:ℤ)=(2:ℕ) by rfl,Nat.cast_smul_eq_nsmul] at px
  rw [←ez,show (5:ℤ)=(5:ℕ) by rfl,Nat.cast_smul_eq_nsmul] at py
  rw [←ez] at hz
  exact large_or_affine odd f onto ab x y z hx hy ne gen (2:Fin 3)
    (mult_span (f z) hz) px py (big z px py)

end HaarMetaPrimitiveCore
#print axioms HaarMetaPrimitiveCore.p025
