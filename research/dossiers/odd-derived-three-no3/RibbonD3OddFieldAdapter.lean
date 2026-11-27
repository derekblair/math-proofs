import RibbonD3OddInterfaces
import RibbonD3FieldUse
import RibbonD3Orientation
import RibbonD3WideInversion
import RibbonD3WideFieldBadBridge

namespace RibbonD3Odd
open RibbonD3Stationary RibbonD3Orientation RibbonDerived3 RibbonP11
open RibbonD3Field (chart)
universe u v

private theorem flip_bad {K : Type v} [Field K] (a b : Kˣ)
    (F : RibbonD3Wide.FieldBad b a) : RibbonD3Wide.FieldBad a b := by
  obtain ⟨p,P,f,x,y,X,Y,M⟩ := F
  have C : (RibbonD3Wide.exactBad.all fun r =>
    decide ((r.1,r.2.2,r.2.1)∈RibbonD3Wide.exactBad))=true := by decide +kernel
  exact ⟨p,P,f,y,x,Y,X,of_decide_eq_true (List.all_eq_true.mp C _ M)⟩

private theorem bind_bad {K : Type v} [Field K] (a b : Kˣ)
    (F : RibbonD3Wide.FieldBad a b) :
    ∃ (p : ℕ), PrimeBad p ∧ ∃ (e : ZMod p→+*K) (a' b' : ZMod p),
      e a'=(a:K) ∧ e b'=(b:K) ∧ RibbonD3WideFinite.Bad (p,a'.val,b'.val) := by
  obtain ⟨p,P,f,x,y,X,Y,M⟩ := F
  exact ⟨p,P,f,x,y,X,Y,(RibbonD3Wide.bad_iff _).mp M⟩

theorem wide_fieldCore_inverse {G : Type u} {K : Type v} [Group G] [Field K]
    (d3 : DLS G 3=⊥) (x y : G)
    (μ : G→*Kˣ) (τ : G→K) (co : IsCocycle μ τ) (a1 : μ x≠1) (tx : τ x=0) (ty : τ y=1)
    (n : Nat) (ho : Odd n) (t : (2:K)≠0) (v : (3:K)≠0)
    (pa : μ x^n=1) (pb : μ y^n=1) :
    LongGood x y ∨ RibbonD3Wide.FieldBad (μ x) (μ y) := by
  rcases RibbonD3Wide.inversion_cover (μ x) (μ y) n ho t v pa pb a1 with ⟨ix,iy,k,u1,sep⟩|F
  · left
    let m : Motion := ⟨ix,iy,false⟩
    let u := (act m x y).1
    let w := (act m x y).2
    have xu : μ u=(if ix then (μ x)⁻¹ else μ x) := by cases ix <;> simp [u,m,act,motionPow]
    have yw : μ w=(if iy then (μ y)⁻¹ else μ y) := by cases iy <;> simp [w,m,act,motionPow]
    have h : Normalized (RingHom.id K) x y μ τ :=
      Or.inl ⟨fun e => a1 (Units.ext e),tx,ty⟩
    obtain ⟨σ,c,norm⟩ := normalize_act m (RingHom.id K) (fun _ e => isUnit_iff_ne_zero.mpr e)
      μ τ co x y h
    rcases norm with ⟨_,ax,ay⟩|⟨eq,_,_,_⟩
    · apply RibbonD3Finite.longUnact m x y
      exact Or.inr (Or.inr (Or.inr (RibbonD3FieldPoint.from_affine d3 u w k μ σ c ax ay (by
        rw [xu,yw]
        exact sep))))
    · exact False.elim (u1 (xu ▸ Units.ext eq))
  · exact Or.inr F

/-- Checked group callback for the non-characteristic-three shadow of an odd-order ribbon. -/
theorem field_from_wide_inverse : FieldCover.{u,v} RibbonD3WideFinite.Bad := by
  intro G K _ _ _ _ d3 x y μ τ two three odd co norm
  have power (g : G) : (μ g)^(Nat.card G)=1 := by rw [←map_pow,pow_card_eq_one',map_one]
  rcases norm with ⟨a,tx,ty⟩|⟨_,b,tx,ty⟩
  · have ne : μ x≠1 := fun e => a (by simp [e])
    exact (wide_fieldCore_inverse d3 x y μ τ co ne tx ty _ odd two three (power x) (power y)).imp
      Or.inl (bind_bad _ _)
  · have ne : μ y≠1 := fun e => b (by simp [e])
    exact (wide_fieldCore_inverse d3 y x μ τ co ne ty tx _ odd two three (power y) (power x)).imp
      (fun L => Or.inl (RibbonD3Finite.longUnact ⟨false,false,true⟩ x y L)) (fun F => bind_bad _ _ (flip_bad _ _ F))

end RibbonD3Odd
#print axioms RibbonD3Odd.field_from_wide_inverse
