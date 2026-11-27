import HaarMetaCyclic15Dispatch
import HaarOrbitCylinderCase

namespace HaarMetaSecondTorsion
open HaarMetaEarlyCases HaarMetaSmallDispatchCore HaarMetaPrimitiveDispatch
open HaarMetaQuotientDispatchCore HaarMetaQuotientGeometry HaarMetaAlgebraCore HaarClass4Generate
variable {G Q : Type*} [Group G] [CommGroup Q]

private theorem cyclic_nine [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (ab : ∀ a b : f.ker, a*b=b*a) (x y t : G)
    (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : Generates x y)
    (fx : f x≠1) (fy : f y≠1) (fne : f x≠f y)
    (card : Nat.card Q=9) (hz : Subgroup.zpowers (f x)=⊤)
    (nt : f t≠1) (dt : (f t)^3=1) (eq : f y=(f x)^2*f t) : Good x y := by
  let ψ := HaarMetaCoordinateIso.orient (f x) hz 9 card
  let F := ψ.toMonoidHom.comp f
  let a : ZMod 9 := (F t).toAdd
  have nn : a≠0 := fun h => nt (ψ.injective (show F t=ψ 1 by rw [map_one]; exact h))
  have da : (3:ℕ) • a=0 := by
    change (F t)^3=1
    change (ψ (f t))^3=1
    rw [←map_pow,dt,map_one]
  let u : Fin 9 := ⟨a.val, ZMod.val_lt a⟩
  have PX : F x=Multiplicative.ofAdd (1:ZMod 9) := by
    change ψ (f x)=_
    simpa using HaarMetaCoordinateIso.orient_zpow (f x) hz 9 card 1
  have PY : F y=Multiplicative.ofAdd ((2*1+u.val:ℕ):ZMod 9) := by
    change ψ (f y)=_
    rw [eq,map_mul,map_pow]
    change (F x)^2 * F t = _
    rw [PX]
    change (2:ℕ) • (1:ZMod 9) + a = _
    simp only [u, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val, two_nsmul, mul_one]; rfl
  have ds := from_projection F x y 1 (2*1+u.val) PX PY
    (fun h => fx (ψ.injective (h.trans (map_one ψ).symm)))
    (fun h => fy (ψ.injective (h.trans (map_one ψ).symm)))
    (fun h => fne (ψ.injective h))
  have aff := HaarMetaSmallAffine.torsion9_shift u (1:Fin 9) (zmod9_gen a nn da) ds
  exact apply_affine F x y _ _ 1 2 (ab_kernel_comp f ψ.toMonoidHom ψ.injective ab)
    hx hy ne gen PX PY (by decide) (by decide) (by decide) (by decide) (by decide) aff
    (fun g X Y ha hx' hy' hn' ge cx cy => one_two odd g X Y ha hx' hy' hn' ge (by simpa using cx) (by simpa using cy))

/-- Complete dispatch for the second torsion relation, relative to the two
cyclic-15 strip solvers. -/
theorem cycle [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : Generates x y)
    (h : (3:ℕ) • (A f y-(2:ℤ) • A f x)=0)
    (run3 : ∀ (g : G→*C 15) (X Y : G), (∀ a b : g.ker, a*b=b*a) →
      X≠1 → Y≠1 → X≠Y → Generates X Y →
      g X=Multiplicative.ofAdd (1:ZMod 15) → g Y=Multiplicative.ofAdd (3:ZMod 15) → Good X Y)
    (run4 : ∀ (g : G→*C 15) (X Y : G), (∀ a b : g.ker, a*b=b*a) →
      X≠1 → Y≠1 → X≠Y → Generates X Y →
      g X=Multiplicative.ofAdd (1:ZMod 15) → g Y=Multiplicative.ofAdd (4:ZMod 15) → Good X Y) :
    Good x y := by
  letI : Finite Q := Finite.of_surjective f onto
  by_cases bad : f x=1 ∨ f y=1 ∨ f x=f y
  · exact collapse_any odd f ab x y hx hy ne bad
  push Not at bad
  let t := y*(x^2)⁻¹
  have ht : A f t = A f y-(2:ℤ) • A f x := by
    apply Additive.ofMul.symm.injective
    change (A f t).toMul = (A f y-(2:ℤ) • A f x).toMul
    simp [t,A,toMul_sub,toMul_zsmul,div_eq_mul_inv]
  have cy : f y=(f x)^2*f t := by
    simp only [t,map_mul,map_inv,map_pow]
    rw [mul_comm ((f x)^2),mul_assoc,inv_mul_cancel,mul_one]
  by_cases ts : f t=1
  · exact ap odd f onto ab x y hx hy ne gen (by simpa [ts] using cy)
  have An : A f y-(2:ℤ) • A f x ≠ 0 := by rw [←ht]; exact ts
  have dt : (f t)^3=1 := by change (3:ℕ) • A f t=0; rw [ht]; exact h
  have at3 : addOrderOf (A f t)=3 := torsion_three _ ts (by rw [ht]; exact h)
  have ord : orderOf (f t)=3 := at3
  have sp : Spans (A f x) (A f t) := by rw [ht]; exact span_shear _ _ 2 (span_after f onto x y gen)
  have all := second_cylinder_cases (A f x) (A f y) (span_after f onto x y gen) (show Odd (Nat.card (Additive Q)) from odd_of_surj (Q:=Q) f onto odd) An h
  dsimp only at all
  rw [←ht] at all
  rcases all with ⟨width,inj⟩|⟨_,card⟩|⟨rel,card⟩|⟨rel,card⟩
  · letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
    apply HaarOrbitCylinderCase.cycle f x y t odd ord cy (Commute.all _ _)
    intro a b E
    let idx (i : Fin 18) : Fin 6 × Fin 3 :=
      (⟨i.val/3, by have := i.isLt; omega⟩, ⟨i.val%3,by omega⟩)
    have H : cylinder (A f t) (A f x) 6 (idx a) = cylinder (A f t) (A f x) 6 (idx b) := by
      simpa only [cylinder,idx,A,HaarOrbitCylinderCase.rep0,map_mul,map_pow, ofMul_mul, ofMul_pow] using congrArg Additive.ofMul E
    have p := congrArg (fun i : Fin 6 × Fin 3 => i.1.val) (inj H)
    have q := congrArg (fun i : Fin 6 × Fin 3 => i.2.val) (inj H)
    change a.val/3=b.val/3 at p
    change a.val%3=b.val%3 at q
    exact Fin.ext (by omega)
  · exact index_three odd f onto ab card x y hx hy ne
  · rcases order_nine_split (A f t) (A f x) sp at3 rel with hz|⟨cx,_⟩
    · exact cyclic_nine odd f ab x y t hx hy ne gen bad.1 bad.2.1 bad.2.2 card (mult_span _ hz) ts dt cy
    · have cY : (3:ℕ) • A f y=0 := by
        change (f y)^3=1
        change (f x)^3=1 at cx
        rw [cy,mul_pow,pow_right_comm (f x) 2 3,cx,one_pow,dt,mul_one]
      exact torus_case odd f onto ab x y gen bad.1 bad.2.1 cx cY card
  · obtain ⟨z,hz⟩ := order_fifteen_cyclic (A f t) (A f x) sp at3 rel
    have dx : (f x)^3≠1 := by
      intro badX
      have k := congrArg (proj (A f t)) (show (3:ℕ) • A f x=0 from badX)
      rw [map_nsmul,map_zero] at k
      have dd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr k
      change relativeOrder (A f t) (A f x) ∣ 3 at dd
      rw [rel] at dd
      omega
    exact HaarMetaCyclic15Dispatch.cycle f ab x y t hx hy ne gen bad.1 bad.2.1 bad.2.2 card z.toMul
      (mult_span _ hz) ts dt dx cy run3 run4

end HaarMetaSecondTorsion
#print axioms HaarMetaSecondTorsion.cycle
