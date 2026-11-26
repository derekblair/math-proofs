import HaarMetaEarlyCases
import HaarMetaSmallAffineTransport
import HaarOrbitC7Case
import HaarOrbitC11Case
import HaarMetaNineHaar

namespace HaarMetaSmallDispatchCore
open HaarMetaEarlyCases HaarClass4Generate HaarAllNoncommuting
variable {G : Type*} [Group G]

abbrev C (n : ℕ) := Multiplicative (ZMod n)

theorem surj_one {m : ℕ} [NeZero m] (f : G→*C m) (x : G)
    (e : f x=Multiplicative.ofAdd (1:ZMod m)) : Function.Surjective f := by
  intro y
  refine ⟨x^y.toAdd.val,?_⟩
  rw [map_pow,e]
  change y.toAdd.val • (1:ZMod m) = y.toAdd
  rw [Nat.smul_one_eq_cast,ZMod.natCast_zmod_val]

theorem one_order {m : ℕ} (f : G→*C m) (x : G)
    (e : f x=Multiplicative.ofAdd (1:ZMod m)) : orderOf (f x)=m := by
  rw [e,orderOf_ofAdd_eq_addOrderOf,ZMod.addOrderOf_one]

theorem apply_affine {m : ℕ} [NeZero m] (f : G→*C m) (x y : G) (p q u v : ℕ)
    (ab : ∀ a b : f.ker, a*b=b*a) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : Generates x y)
    (px : f x=Multiplicative.ofAdd (p:ZMod m)) (py : f y=Multiplicative.ofAdd (q:ZMod m))
    (hu : u<m) (hv : v<m) (nu : u≠0) (nv : v≠0) (duv : u≠v)
    (k : HaarMetaSmallAffine.Affine m p q u v)
    (run : ∀ (g : G→*C m) (X Y : G), (∀ a b : g.ker, a*b=b*a) →
      X≠1 → Y≠1 → X≠Y → Generates X Y →
      g X=Multiplicative.ofAdd (u:ZMod m) → g Y=Multiplicative.ofAdd (v:ZMod m) →
      Good X Y) : Good x y := by
  obtain ⟨g,σ,ker,ex,ey⟩ := HaarMetaSmallAffineTransport.transport
    f x y p q u v px py hu hv nu nv duv k
  let X := HaarMetaPermute.ports x y (σ 1) * (HaarMetaPermute.ports x y (σ 0))⁻¹
  let Y := HaarMetaPermute.ports x y (σ 2) * (HaarMetaPermute.ports x y (σ 0))⁻¹
  have h : ∀ a b : g.ker, a*b=b*a := by rw [ker]; exact ab
  obtain ⟨a,b,c⟩ := HaarMetaPermute.normalized_distinct x y σ hx hy ne
  obtain ⟨n,hn,cy⟩ := run g X Y h a b c (HaarMetaPermute.normalized_generates x y σ gen) ex ey
  exact ⟨n,hn,HaarMetaPermute.normalizedCycle x y σ cy⟩

theorem one_two [Finite G] {m : ℕ} [NeZero m] (odd : Odd (Nat.card G))
    (f : G→*C m) (x y : G) (ab : ∀ a b : f.ker, a*b=b*a)
    (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : Generates x y)
    (px : f x=Multiplicative.ofAdd (1:ZMod m)) (py : f y=Multiplicative.ofAdd (2:ZMod m)) :
    Good x y := by
  apply ap odd f (surj_one f x px) ab x y hx hy ne gen
  rw [px,py]
  change (2:ZMod m)=2 • (1:ZMod m)
  rw [Nat.smul_one_eq_cast]
  norm_num

theorem one_three [Finite G] {m : ℕ} (odd : Odd (Nat.card G))
    (f : G→*C m) (x y : G) (ab : ∀ a b : f.ker, a*b=b*a)
    (px : f x=Multiplicative.ofAdd (1:ZMod m)) (py : f y=Multiplicative.ofAdd (3:ZMod m))
    (sm : m=7 ∨ m=9 ∨ m=11) : Good x y := by
  letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
  have h : f y=(f x)^(3:ℕ) := by
    rw [px,py]
    change (3:ZMod m)=3 • (1:ZMod m)
    rw [Nat.smul_one_eq_cast]
    norm_num
  rcases sm with rfl|rfl|rfl
  · exact HaarOrbitC7Case.cycle f x y odd (one_order f x px) h
  · exact HaarMetaNineHaar.kernel_odd f x y (by rw [px];rfl) (by rw [py];rfl) (surj_one f x px)
      (Odd.of_dvd_nat odd f.ker.card_subgroup_dvd_card)
  · exact HaarOrbitC11Case.cycle f x y odd (one_order f x px) h

end HaarMetaSmallDispatchCore
#print axioms HaarMetaSmallDispatchCore.one_three
