import HaarMetaPermute
import HaarMetaSmallAffine
import Mathlib.Data.ZMod.Basic

namespace HaarMetaSmallAffineTransport

open HaarMetaSmallAffine

variable {G : Type*} [Group G] {n : ℕ} [NeZero n]

private def scaled (a : ZMod n) : Multiplicative (ZMod n) →* Multiplicative (ZMod n) where
  toFun z := Multiplicative.ofAdd (a * z.toAdd)
  map_one' := by change a * 0 = 0; exact mul_zero a
  map_mul' z w := by
    change a * (z.toAdd + w.toAdd) = a*z.toAdd + a*w.toAdd
    exact mul_add _ _ _

omit [NeZero n] in
private theorem scaled_one_iff (a : (ZMod n)ˣ) (z : Multiplicative (ZMod n)) :
    scaled (a : ZMod n) z = 1 ↔ z = 1 := by
  constructor
  · intro h
    change (a : ZMod n) * z.toAdd = 0 at h
    change z.toAdd = 0
    have h' := congrArg (fun w : ZMod n => (↑a⁻¹ : ZMod n) * w) h
    simpa [← mul_assoc, ← Units.val_mul] using h'
  · rintro rfl
    exact map_one _

/-- An arithmetic affine certificate gives a scaling of the quotient homomorphism
with identical kernel, and a group-port permutation whose normalized images are
the two prescribed target residues. -/
theorem transport (f : G →* Multiplicative (ZMod n)) (x y : G) (p q u v : ℕ)
    (hp : f x = Multiplicative.ofAdd (p : ZMod n))
    (hq : f y = Multiplicative.ofAdd (q : ZMod n))
    (hu : u < n) (hv : v < n) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h : Affine n p q u v) :
    ∃ (g : G →* Multiplicative (ZMod n)) (σ : Equiv.Perm (Fin 3)), g.ker = f.ker ∧
      g (HaarMetaPermute.ports x y (σ 1) * (HaarMetaPermute.ports x y (σ 0))⁻¹) =
        Multiplicative.ofAdd (u : ZMod n) ∧
      g (HaarMetaPermute.ports x y (σ 2) * (HaarMetaPermute.ports x y (σ 0))⁻¹) =
        Multiplicative.ofAdd (v : ZMod n) := by
  obtain ⟨a,b,ha,hm⟩ := h
  let A := ZMod.unitOfCoprime a.val ha
  let g := (scaled (A : ZMod n)).comp f
  have hA : (A : ZMod n) = (a.val : ZMod n) := ZMod.coe_unitOfCoprime _ _
  let r := HaarMetaPermute.ports x y
  let τ : Fin 3 → ℕ := ![0,u,v]
  have hτ : Function.Injective τ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [τ, Ne.symm hu0, Ne.symm hv0, Ne.symm huv]
  have hτlt (i : Fin 3) : τ i < n := by
    fin_cases i <;> simp [τ, Nat.pos_of_ne_zero (NeZero.ne n), hu, hv]
  have hval (z : ℕ) :
      ((a.val : ZMod n) * (z : ZMod n) + b.val).val = (a.val*z+b.val) % n := by
    simpa only [Nat.cast_add, Nat.cast_mul] using (ZMod.val_natCast n (a.val*z+b.val))
  have hlabel (i : Fin 3) : ∃ j : Fin 3, (g (r j)).toAdd + (b.val : ZMod n) = τ i := by
    have hchoose : τ i = b.val ∨ τ i = (a.val*p+b.val)%n ∨ τ i = (a.val*q+b.val)%n := by
      apply (hm ⟨τ i,hτlt i⟩).mpr
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have key (z : ZMod n) (hz : z.val = τ i) : z = (τ i : ZMod n) := by
      rw [← hz, ZMod.natCast_zmod_val]
    rcases hchoose with e | e | e
    · refine ⟨0,key _ ?_⟩
      simpa [r, HaarMetaPermute.ports, g, scaled, ZMod.val_natCast_of_lt b.isLt] using e.symm
    · refine ⟨1,key _ ?_⟩
      simpa [r, HaarMetaPermute.ports, g, scaled, hp, hA, hval] using e.symm
    · refine ⟨2,key _ ?_⟩
      simpa [r, HaarMetaPermute.ports, g, scaled, hq, hA, hval] using e.symm
  choose s hs using hlabel
  have hsInj : Function.Injective s := by
    intro i j e
    apply hτ
    have hh : ((τ i : ℕ) : ZMod n) = ((τ j : ℕ) : ZMod n) := (hs i).symm.trans (e ▸ hs j)
    have hhv := congrArg ZMod.val hh
    simpa only [ZMod.val_natCast_of_lt (hτlt i), ZMod.val_natCast_of_lt (hτlt j)] using hhv
  let σ := Equiv.ofBijective s ⟨hsInj,Finite.surjective_of_injective hsInj⟩
  refine ⟨g, σ, ?_, ?_, ?_⟩
  · ext z
    exact scaled_one_iff A (f z)
  · have h0 : (g (r (σ 0))).toAdd + (b.val : ZMod n) = 0 := by
      change (g (r (s 0))).toAdd + (b.val : ZMod n) = 0
      simpa [τ] using hs 0
    have h1 : (g (r (σ 1))).toAdd + (b.val : ZMod n) = (u : ZMod n) := hs 1
    rw [map_mul, map_inv]
    change (g (r (σ 1))).toAdd + -(g (r (σ 0))).toAdd = (u : ZMod n)
    linear_combination h1 - h0
  · have h0 : (g (r (σ 0))).toAdd + (b.val : ZMod n) = 0 := by
      change (g (r (s 0))).toAdd + (b.val : ZMod n) = 0
      simpa [τ] using hs 0
    have h2 : (g (r (σ 2))).toAdd + (b.val : ZMod n) = (v : ZMod n) := hs 2
    rw [map_mul, map_inv]
    change (g (r (σ 2))).toAdd + -(g (r (σ 0))).toAdd = (v : ZMod n)
    linear_combination h2 - h0

end HaarMetaSmallAffineTransport

#print axioms HaarMetaSmallAffineTransport.transport
