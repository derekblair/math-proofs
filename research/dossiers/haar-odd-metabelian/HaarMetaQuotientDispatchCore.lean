import HaarMetaPrimitiveDispatch
import HaarMetaQuotientGeometryTorus
import HaarMetaTorusHaar

namespace HaarMetaQuotientDispatchCore
open HaarMetaQuotientGeometry HaarMetaAlgebraCore HaarMetaEarlyCases HaarMetaSmallDispatchCore
variable {G Q : Type*} [Group G] [CommGroup Q]

abbrev A (f : G→*Q) (x : G) := Additive.ofMul (f x)

theorem mult_span (z : Q) (h : AddSubgroup.zmultiples (Additive.ofMul z)=⊤) :
    Subgroup.zpowers z=⊤ := by
  rw [Subgroup.eq_top_iff']
  intro q
  have qin : Additive.ofMul q ∈ AddSubgroup.zmultiples (Additive.ofMul z) := by rw [h]; trivial
  obtain ⟨i,hi⟩ := AddSubgroup.mem_zmultiples_iff.mp qin
  exact ⟨i,hi⟩

theorem torus_case [Finite G] [Finite Q] (odd : Odd (Nat.card G))
    (f : G→*Q) (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (gen : HaarClass4Generate.Generates x y)
    (hx : f x≠1) (hy : f y≠1) (hX : (3:ℕ) • A f x=0) (hY : (3:ℕ) • A f y=0)
    (card : Nat.card Q=9) : Good x y := by
  have oX : addOrderOf (A f x)=3 := torsion_three _ hx hX
  have oY : addOrderOf (A f y)=3 := torsion_three _ hy hY
  have span : Spans (A f y) (A f x) := span_swap _ _ (span_after f onto x y gen)
  have rc := relative_card (A f x) (A f y) span oX
  have rel : relativeOrder (A f x) (A f y)=3 := by
    change Nat.card Q = _ at rc
    omega
  let θ := torusCoordinates (A f x) (A f y) oX span rel oY
  let e : Q ≃* Multiplicative (ZMod 3 × ZMod 3) :=
    { toFun := fun q => Multiplicative.ofAdd (θ.symm (Additive.ofMul q))
      invFun := fun a => (θ a.toAdd).toMul
      left_inv := θ.apply_symm_apply
      right_inv := θ.symm_apply_apply
      map_mul' := θ.symm.map_add }
  let g := e.toMonoidHom.comp f
  have abg := ab_kernel_comp f e.toMonoidHom e.injective ab
  letI : Fact (∀ a b : g.ker, a*b=b*a) := ⟨abg⟩
  have gx : (g x).toAdd=(0,1) := by
    change θ.symm (A f x)=(0,1)
    apply θ.injective
    rw [θ.apply_symm_apply]
    change A f x = (0:ZMod 3).val • A f y + (1:ZMod 3).val • A f x
    rw [show (1:ZMod 3).val=1 by rfl]; simp
  have gy : (g y).toAdd=(1,0) := by
    change θ.symm (A f y)=(1,0)
    apply θ.injective
    rw [θ.apply_symm_apply]
    change A f y = (1:ZMod 3).val • A f y + (0:ZMod 3).val • A f x
    rw [show (1:ZMod 3).val=1 by rfl]; simp
  exact HaarMetaTorusHaar.kernel_odd g x y gx gy (e.surjective.comp onto)
    (Odd.of_dvd_nat odd g.ker.card_subgroup_dvd_card)

theorem zmod9_gen (a : ZMod 9) (ne : a≠0) (cu : (3:ℕ) • a=0) :
    HaarMetaSmallAffine.NonzeroThreeOrderGenerators 9 a.val 1 := by
  revert a
  decide

theorem zmod15_gen (a b : ZMod 15) (ne : a≠0) (cu : (3:ℕ) • a=0)
    (nb : (3:ℕ) • b≠0) :
    HaarMetaSmallAffine.NonzeroThreeOrderGenerators 15 a.val b.val := by
  revert a b
  decide

end HaarMetaQuotientDispatchCore
#print axioms HaarMetaQuotientDispatchCore.torus_case
