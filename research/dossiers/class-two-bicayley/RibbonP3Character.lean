import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

namespace RibbonP3
variable {G : Type*} [Group G]

/-- Exact transport to the single F3 character coordinate: compare two class-
three tails after equality of the low c-residue has been established in
the class-two quotient. The homomorphism may be defined on any subgroup
containing c³, u, and v. -/
theorem tail_character (c u v : G) (S : Subgroup G)
    (hc : c^3∈S) (hu : u∈S) (hv : v∈S)
    (f : S →* Multiplicative (ZMod 3)) (q t : ℤ)
    (fc : f ⟨c^3,hc⟩ = Multiplicative.ofAdd (t:ZMod 3))
    (fu : f ⟨u,hu⟩ = Multiplicative.ofAdd (1:ZMod 3))
    (fv : f ⟨v,hv⟩ = Multiplicative.ofAdd (q:ZMod 3))
    (k l m k' l' m' : ℤ) (low : k%3=k'%3)
    (e : c^k*u^l*v^m=c^k'*u^l'*v^m') :
     (l+q*m+t*(k/3))%3=(l'+q*m'+t*(k'/3))%3 := by
  have split (z : ℤ) : c^z=c^(z%3)*(c^3)^(z/3) := by
    have ez : z%3+3*(z/3)=z := by rw [Int.mul_comm 3,Int.emod_add_ediv_mul]
    have ec : c^((3:ℤ)*(z/3))=(c^3)^(z/3) := by simp only [zpow_mul, zpow_ofNat]
    rw [← ec, ← zpow_add,ez]
  have H : (c^3)^(k/3)*u^l*v^m=(c^3)^(k'/3)*u^l'*v^m' := by
    apply mul_left_cancel (a:=c^(k%3))
    simpa only [split k,split k',← low,mul_assoc] using e
  let C : S := ⟨c^3,hc⟩
  let U : S := ⟨u,hu⟩
  let V : S := ⟨v,hv⟩
  have hh : C^(k/3)*U^l*V^m = C^(k'/3)*U^l'*V^m' := Subtype.ext H
  have h := congrArg f hh
  change f C = _ at fc
  change f U = _ at fu
  change f V = _ at fv
  simp only [map_mul,map_zpow,fc,fu,fv] at h
  change (k/3) • (t:ZMod 3) + l • (1:ZMod 3) + m • (q:ZMod 3) =
    (k'/3) • (t:ZMod 3) + l' • (1:ZMod 3) + m' • (q:ZMod 3) at h
  apply (ZMod.intCast_eq_intCast_iff' (l+q*m+t*(k/3)) (l'+q*m'+t*(k'/3)) 3).mp
  push_cast
  simpa only [zsmul_eq_mul,mul_one,mul_comm,add_assoc,add_comm,add_left_comm] using h

end RibbonP3
#print axioms RibbonP3.tail_character
