import HaarMetaSmallDispatchCore
import HaarMetaCoordinateIso

namespace HaarMetaPrimitiveDispatch
open HaarMetaEarlyCases HaarMetaSmallDispatchCore HaarClass4Generate HaarMetaAlgebraCore
open HaarMetaSmallAffine
variable {G Q : Type*} [Group G] [Group Q]

theorem collapse_any [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (ab : ∀ a b : f.ker, a*b=b*a) (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y)
    (h : f x=1 ∨ f y=1 ∨ f x=f y) : Good x y := by
  rcases h with c|c|c
  · exact collapse odd f ab x y hx hy ne c
  · obtain ⟨n,h,cy⟩ := collapse odd f ab y x hy hx ne.symm c
    exact ⟨n,h,HaarK33Haar.swap_cycle x y cy⟩
  · let σ : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 0 2)
    have s0 : σ 0=1 := by decide
    have s1 : σ 1=2 := by decide
    let X := HaarMetaPermute.ports x y (σ 1)*(HaarMetaPermute.ports x y (σ 0))⁻¹
    let Y := HaarMetaPermute.ports x y (σ 2)*(HaarMetaPermute.ports x y (σ 0))⁻¹
    have fx : f X=1 := by simp [X,s0,s1,HaarMetaPermute.ports,c]
    obtain ⟨hX,hY,r⟩ := HaarMetaPermute.normalized_distinct x y σ hx hy ne
    obtain ⟨n,hn,cy⟩ := collapse odd f ab X Y hX hY r fx
    exact ⟨n,hn,HaarMetaPermute.normalizedCycle x y σ cy⟩

theorem residues_distinct {m : ℕ} [NeZero m] {p q : ℕ}
    (hp : (p:ZMod m)≠0) (hq : (q:ZMod m)≠0) (hne : (p:ZMod m)≠(q:ZMod m)) :
    HaarMetaSmallAffine.Distinct m p q := by
  refine ⟨?_,?_,?_⟩
  · exact fun h => hp (ZMod.val_injective m (by simpa using h))
  · exact fun h => hq (ZMod.val_injective m (by simpa using h))
  · exact fun h => hne (ZMod.val_injective m (by simpa using h))

theorem from_projection {m : ℕ} [NeZero m] (f : G→*C m) (x y : G) (p q : ℕ)
    (px : f x=Multiplicative.ofAdd (p:ZMod m)) (py : f y=Multiplicative.ofAdd (q:ZMod m))
    (hx : f x≠1) (hy : f y≠1) (hne : f x≠f y) : Distinct m p q := by
  apply residues_distinct
  · intro e
    exact hx (by rw [px,e];rfl)
  · intro e
    exact hy (by rw [py,e];rfl)
  · intro e
    exact hne (by rw [px,py,e])

theorem large_or_affine [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q) (onto : Function.Surjective f)
    (ab : ∀ a b : f.ker, a*b=b*a) (x y z : G) (hx : x≠1) (hy : y≠1) (ne : x≠y)
    (gen : Generates x y) (k : Fin 3)
    (hz : Subgroup.zpowers (f z)=⊤)
    (px : f x=(f z)^(primitivePattern k).1)
    (py : f y=(f z)^(primitivePattern k).2.1)
    (big : (primitivePattern k).2.2≤orderOf (f z) → Good x y) : Good x y := by
  classical
  by_cases bigYes : (primitivePattern k).2.2≤orderOf (f z)
  · exact big bigYes
  by_cases bad : f x=1 ∨ f y=1 ∨ f x=f y
  · exact collapse_any odd f ab x y hx hy ne bad
  push Not at bad
  let m := Nat.card Q
  have card : Nat.card Q=m := rfl
  have e : orderOf (f z)=m := orderOf_eq_card_of_zpowers_eq_top hz
  have oddQ : Odd m := odd_of_surj f onto odd
  have large3 : 3≤m := by
    have mn : m≠1 := by
      intro eq
      have u : f z=1 := orderOf_eq_one_iff.mp (e.trans eq)
      exact bad.1 (by simpa [u] using px)
    obtain ⟨i,h⟩ := oddQ
    omega
  have width : (primitivePattern k).2.2≤13 := by fin_cases k <;> decide
  have sm : m<13 := by omega
  letI : NeZero m := ⟨by omega⟩
  let ψ := HaarMetaCoordinateIso.orient (f z) hz m card
  let F := ψ.toMonoidHom.comp f
  have abF := ab_kernel_comp f ψ.toMonoidHom ψ.injective ab
  let p := (primitivePattern k).1
  let q := (primitivePattern k).2.1
  have cast (u : G) (i : ℕ) (h : f u=(f z)^i) :
      F u = Multiplicative.ofAdd (i:ZMod m) := by
    change ψ (f u)=_
    rw [h,←zpow_natCast]
    simpa only [Int.cast_natCast] using HaarMetaCoordinateIso.orient_zpow (f z) hz m card (i:ℤ)
  have FX := cast x p px
  have FY := cast y q py
  have distinct := from_projection F x y p q FX FY
    (fun h => bad.1 (ψ.injective (h.trans (map_one ψ).symm)))
    (fun h => bad.2.1 (ψ.injective (h.trans (map_one ψ).symm)))
    (fun h => bad.2.2 (ψ.injective h))
  have mod : m%2=1 := by obtain ⟨i,r⟩ := oddQ; omega
  have H := HaarMetaSmallAffine.primitive k ⟨m,sm⟩ large3 mod (by change m < (primitivePattern k).2.2; omega) distinct
  rcases H with ap'|⟨hs,case13⟩
  · exact apply_affine F x y p q 1 2 abF hx hy ne gen FX FY (by omega) (by omega)
      (by decide) (by decide) (by decide) ap' (fun g X Y ha hx' hy' hn' ge cx cy =>
        one_two odd g X Y ha hx' hy' hn' ge (by simpa using cx) (by simpa using cy))
  · have m4 : 3<m := by rcases hs with h|h|h <;> change m = _ at h <;> omega
    exact apply_affine F x y p q 1 3 abF hx hy ne gen FX FY (by omega) m4
      (by decide) (by decide) (by decide) case13 (fun g X Y ha _ _ _ _ cx cy =>
        one_three odd g X Y ha (by simpa using cx) (by simpa using cy) (by simpa using hs))

end HaarMetaPrimitiveDispatch
#print axioms HaarMetaPrimitiveDispatch.large_or_affine
