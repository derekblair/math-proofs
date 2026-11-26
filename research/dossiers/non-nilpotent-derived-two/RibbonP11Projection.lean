import RibbonP11PrimeModel
import RibbonP11ChartFromRing
import RibbonP11Trichotomy
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace RibbonP11
open RibbonAffine HaarClass4Generate HaarClass4Ports
variable {G : Type*} [Group G]
variable {K S T : Type*} [Field K] [CommRing S] [CommRing T]

theorem map_equivariant (f : S→+*T) (μ : G→*Sˣ) (ell : D G→*Multiplicative S)
    (h : Equivariant μ ell) :
    Equivariant ((Units.map f.toMonoidHom).comp μ) (f.toAddMonoidHom.toMultiplicative.comp ell) := by
  intro g d
  change f (Multiplicative.toAdd (ell (MulAut.conjNormal g d))) =
    f (μ g:S)*f (Multiplicative.toAdd (ell d))
  rw [h,map_mul]

theorem map_cocycle (f : S→+*T) (μ : G→*Sˣ) (τ : G→S)
    (c : IsCocycle μ τ) :
    IsCocycle ((Units.map f.toMonoidHom).comp μ) (f∘τ) := by
  constructor
  · change f (τ 1)=0
    rw [c.1,map_zero]
  · intro g h
    change f (τ (g*h))=f (τ g)+f (μ g:S)*f (τ h)
    rw [c.2,map_add,map_mul]

/-- The two port multipliers determine any residue algebra map. -/
theorem quotient_hom_ext (p : ℕ) (x y : G) (gen : Generates x y)
    (I : Ideal (PA G p)) [Algebra (ZMod p) T]
    (f g : (PA G p ⧸ I) →ₐ[ZMod p] T)
    (X : f (Ideal.Quotient.mk I (gIn p x)) = g (Ideal.Quotient.mk I (gIn p x)))
    (Y : f (Ideal.Quotient.mk I (gIn p y)) = g (Ideal.Quotient.mk I (gIn p y))) : f=g := by
  let j := Ideal.Quotient.mkₐ (ZMod p) I
  let F := f.comp j
  let H := g.comp j
  let f' := F.toMonoidHom.comp (gIn p)
  let g' := H.toMonoidHom.comp (gIn p)
  have eq : Subgroup.closure ({x,y} : Set G) ≤ f'.eqLocus g' := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
    rcases ha with rfl|rfl
    · exact X
    · exact Y
  change Subgroup.closure ({x,y} : Set G)=⊤ at gen
  rw [gen] at eq
  have line : F=H := by
    apply (MonoidAlgebra.lift (ZMod p) T (Abelianization G)).symm.injective
    apply MonoidHom.ext
    intro a
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (commutator G) a
    exact (eq (Subgroup.mem_top b) : b∈f'.eqLocus g')
  apply AlgHom.ext
  intro a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective (I:=I) a
  exact DFunLike.congr_fun line b

section Dual
variable [Algebra K S]

/-- Build the actual dual-number algebra map from the coordinatewise
Leibniz law, with the same multiplication as the finite chart checker. -/
def jetAlg (f : S→ₐ[K]K) (δ : S→ₗ[K]K)
    (der : ∀ r s : S, δ (r*s)=f r*δ s+δ r*f s) :
    S→ₐ[K]TrivSqZeroExt K K := by
  have z : δ 1 = 0 := by
    have h := der 1 1
    have F : f (1:S)=1 := map_one f
    rw [one_mul,F,one_mul,mul_one] at h
    linear_combination -h
  have const (a : K) : δ (algebraMap K S a)=0 := by
    have V : algebraMap K S a = a • (1:S) := by simp [Algebra.smul_def]
    rw [V,map_smul,z,smul_zero]
  exact
    { toFun := fun r => (f r,δ r)
      map_one' := TrivSqZeroExt.ext f.map_one z
      map_zero' := TrivSqZeroExt.ext f.map_zero δ.map_zero
      map_add' := fun r s => TrivSqZeroExt.ext (f.map_add r s) (δ.map_add r s)
      map_mul' := fun r s => TrivSqZeroExt.ext (f.map_mul r s) (by
        change δ (r*s) = f r • δ s + (MulOpposite.op (f s)) • δ r
        rw [op_smul_eq_smul,smul_eq_mul,smul_eq_mul,mul_comm (f s)]
        exact der r s)
      commutes' := fun a => TrivSqZeroExt.ext (f.commutes a) (const a) }

theorem jetAlg_fst (f : S→ₐ[K]K) (δ : S→ₗ[K]K) (der) (r : S) :
    (jetAlg f δ der r).fst=f r := rfl

theorem jetAlg_snd (f : S→ₐ[K]K) (δ : S→ₗ[K]K) (der) (r : S) :
    (jetAlg f δ der r).snd=δ r := rfl

end Dual

end RibbonP11
#print axioms RibbonP11.quotient_hom_ext
#print axioms RibbonP11.jetAlg
