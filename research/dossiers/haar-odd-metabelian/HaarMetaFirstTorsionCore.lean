import HaarMetaQuotientDispatchCore

namespace HaarMetaFirstTorsionCore
open HaarMetaQuotientDispatchCore HaarMetaQuotientGeometry HaarMetaAlgebraCore
open HaarMetaEarlyCases HaarMetaSmallDispatchCore HaarMetaPrimitiveDispatch HaarMetaSmallAffine
variable {G Q : Type*} [Group G] [CommGroup Q]

theorem first [Finite G] [Finite Q] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : HaarClass4Generate.Generates x y)
    (h3 : (f x)^3=1)
    (wide : Function.Injective (fun u : Fin 4 × Fin 3 => f (y^u.1.val*x^u.2.val)) → Good x y) :
    Good x y := by
  classical
  by_cases bad : f x=1 ∨ f y=1 ∨ f x=f y
  · exact collapse_any odd f ab x y hx hy ne bad
  push Not at bad
  have span : Spans (A f x) (A f y) := span_after f onto x y gen
  have h3a : (3:ℕ) • A f x=0 := h3
  have oddQ : Odd (Nat.card Q) := odd_of_surj f onto odd
  have cases := first_cylinder_cases (A f x) (A f y) span oddQ bad.1 h3a
  rcases cases with ⟨_,inj⟩|⟨_,card⟩|⟨rel,card⟩
  · apply wide
    intro u v e
    apply inj
    change f (y^u.1.val*x^u.2.val)=f (y^v.1.val*x^v.2.val) at e
    rw [map_mul,map_mul,map_pow,map_pow,map_pow,map_pow] at e
    exact e
  · exact index_three odd f onto ab card x y hx hy ne
  · have ord := torsion_three (A f x) bad.1 h3a
    rcases order_nine_split (A f x) (A f y) (span_swap _ _ span) ord rel with cyc | ⟨cube,_⟩
    · have hz := mult_span (f y) cyc
      let ψ := HaarMetaCoordinateIso.orient (f y) hz 9 card
      let g := ψ.toMonoidHom.comp f
      let t := (g x).toAdd
      have gx : g x = Multiplicative.ofAdd (t.val:ZMod 9) := by rw [ZMod.natCast_zmod_val]; rfl
      have gy : g y = Multiplicative.ofAdd (1:ZMod 9) := by
        have w := HaarMetaCoordinateIso.orient_zpow (f y) hz 9 card (1:ℤ)
        simpa [g,ψ] using w
      have badx : g x≠1 := fun h => bad.1 (ψ.injective (h.trans (map_one ψ).symm))
      have bady : g y≠1 := fun h => bad.2.1 (ψ.injective (h.trans (map_one ψ).symm))
      have diff : g x≠g y := fun h => bad.2.2 (ψ.injective h)
      have tne : t≠0 := badx
      have cube : (3:ℕ) • t=0 := by
        change (g x)^3=1
        rw [←map_pow, MonoidHom.comp_apply,map_pow,h3,map_one]
      have d := from_projection g x y t.val 1 gx (by simpa using gy) badx bady diff
      let i : Fin 9 := ⟨t.val,ZMod.val_lt _⟩
      have H := torsion9_pair i (1:Fin 9) (zmod9_gen t tne cube) d
      exact apply_affine g x y t.val 1 1 3 (ab_kernel_comp f ψ.toMonoidHom ψ.injective ab)
        hx hy ne gen gx (by simpa using gy) (by decide) (by decide) (by decide) (by decide) (by decide)
        H (fun k X Y ak _ _ _ _ kx ky => one_three odd k X Y ak (by simpa using kx) (by simpa using ky) (Or.inr (Or.inl rfl)))
    · exact torus_case odd f onto ab x y gen bad.1 bad.2.1 h3a cube card

end HaarMetaFirstTorsionCore
#print axioms HaarMetaFirstTorsionCore.first
