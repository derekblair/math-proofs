import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

namespace RibbonP11
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

/-- Linear extension by zero on constants gives the first-jet Leibniz law
once the functional annihilates all products in the residue kernel. -/
theorem leibniz (f : S →ₐ[K] K) (δ : S →ₗ[K] K)
    (constants : ∀ a : K, δ (algebraMap K S a)=0)
    (products : ∀ r s : S, f r=0 → f s=0 → δ (r*s)=0)
    (r s : S) : δ (r*s)=f r*δ s+δ r*f s := by
  let a := algebraMap K S (f r)
  let b := algebraMap K S (f s)
  have fa : f a=f r := f.commutes (f r)
  have fb : f b=f s := f.commutes (f s)
  have H := products (r-a) (s-b) (by simp [fa]) (by simp [fb])
  have c : δ (a*b)=0 := by
    dsimp [a,b]
    rw [← map_mul,constants]
  have L : δ (a*s)=f r*δ s := by
    rw [←Algebra.smul_def,map_smul,smul_eq_mul]
  have M : δ (r*b)=δ r*f s := by
    rw [mul_comm r,←Algebra.smul_def,map_smul,smul_eq_mul,mul_comm]
  rw [sub_mul,mul_sub,mul_sub,map_sub,map_sub,map_sub,c,L,M] at H
  linear_combination H

/-- Surjectivity of (residue, first derivative). Combined with
`leibniz`, this supplies the dual-number ring quotient coordinatewise. -/
theorem jet_surjective (f : S →ₐ[K] K) (δ : S →ₗ[K] K)
    (constants : ∀ a : K, δ (algebraMap K S a)=0)
    (w : S) (fw : f w=0) (nw : δ w≠0) :
    Function.Surjective (fun r => (f r,δ r)) := by
  intro a
  refine ⟨algebraMap K S a.fst + (a.snd / δ w) • w,Prod.ext ?_ ?_⟩
  · change f (algebraMap K S a.fst + (a.snd / δ w) • w)=a.fst
    rw [map_add,f.commutes,map_smul,fw,smul_zero,add_zero]
    rfl
  · change δ (algebraMap K S a.fst + (a.snd / δ w) • w)=a.snd
    rw [map_add,constants,map_smul,zero_add,smul_eq_mul,div_mul_cancel₀ _ nw]

/-- Detecting a nonzero cotangent class produces the full first jet. -/
theorem cotangent_jet (f : S →ₐ[K] K)
    (w : S) (hw : f w=0) (fresh : w ∉ (RingHom.ker f.toRingHom)^2) :
    ∃ δ : S →ₗ[K] K, δ w≠0 ∧
      (∀ r s : S, δ (r*s)=f r*δ s+δ r*f s) ∧
      Function.Surjective (fun r => (f r,δ r)) := by
  let J := RingHom.ker f.toRingHom
  let P := (J^2).restrictScalars K
  let C := LinearMap.range (Algebra.linearMap K S)
  have sub : J^2 ≤ J := by rw [pow_two]; exact Ideal.mul_le_left
  have nf : w ∉ C ⊔ P := by
    intro h
    obtain ⟨a,ha,b,hb,ab⟩ := Submodule.mem_sup.mp h
    obtain ⟨k,rfl⟩ := ha
    have hb' : b ∈ J^2 := hb
    have z : f b=0 := sub hb'
    change algebraMap K S k+b=w at ab
    have eq := congrArg f ab
    rw [map_add,f.commutes,z,hw,add_zero] at eq
    change k=0 at eq
    rw [eq,map_zero,zero_add] at ab
    exact fresh (ab ▸ hb')
  obtain ⟨δ,nz,KZ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem nf
    (inferInstance : Module.Projective K (S ⧸ (C ⊔ P)))
  have kills (r : S) (hr : r∈C ⊔ P) : δ r=0 := by
    have h := Submodule.mem_map_of_mem (f:=δ) hr
    rw [KZ,Submodule.mem_bot] at h
    exact h
  have const (a : K) : δ (algebraMap K S a)=0 :=
    kills _ ((show C ≤ C ⊔ P from le_sup_left) (show algebraMap K S a∈C from ⟨a,rfl⟩))
  have prod (r s : S) (hr : f r=0) (hs : f s=0) : δ (r*s)=0 :=
    kills _ ((show P ≤ C ⊔ P from le_sup_right) (show r*s∈P from by
      change r*s∈J^2
      rw [pow_two]
      exact Ideal.mul_mem_mul hr hs))
  exact ⟨δ,nz,leibniz f δ const prod,jet_surjective f δ const w hw nz⟩

end RibbonP11
#print axioms RibbonP11.jet_surjective
#print axioms RibbonP11.cotangent_jet
