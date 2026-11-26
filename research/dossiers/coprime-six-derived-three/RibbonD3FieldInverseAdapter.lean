import RibbonD3FieldAdapterCommon

namespace RibbonD3Finite
open RibbonD3Stationary RibbonD3Orientation RibbonD3Field RibbonDerived3 RibbonP11
universe u v

def InverseScalarCover : Prop := ∀ {K : Type v} [Field K] (a b : Kˣ) (n : Nat),
  Odd n → (¬3∣n) → (2:K)≠0 → (3:K)≠0 → a^n=1 → b^n=1 → a≠1 →
  (∃ ix iy : Bool, ∃ k : RibbonD3Field.Count,
    (if ix then a⁻¹ else a)≠1 ∧
    Separates (chart k) (if ix then a⁻¹ else a) (if iy then b⁻¹ else b)) ∨ FieldBad a b

theorem fieldCore_inverse {G : Type u} {K : Type v} [Group G] [Field K]
    (SC : InverseScalarCover.{v}) (d3 : DLS G 3=⊥) (x y : G)
    (μ : G→*Kˣ) (τ : G→K) (co : IsCocycle μ τ) (a1 : μ x≠1) (tx : τ x=0) (ty : τ y=1)
    (n : Nat) (ho : Odd n) (h3 : ¬3∣n) (t : (2:K)≠0) (v : (3:K)≠0)
    (pa : μ x^n=1) (pb : μ y^n=1) :
    LongGood x y ∨ FieldBad (μ x) (μ y) := by
  rcases SC (μ x) (μ y) n ho h3 t v pa pb a1 with ⟨ix,iy,k,u1,sep⟩|F
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
    · apply longUnact m x y
      apply embed_long (RibbonD3FieldPoint.from_affine d3 u w k μ σ c ax ay ?_)
      rw [xu,yw]
      exact sep
    · exact False.elim (u1 (xu ▸ Units.ext eq))
  · exact Or.inr F

theorem field_from_inverse (SC : InverseScalarCover.{v}) : FieldCover.{u,v} Bad := by
  intro G K _ _ _ _ d3 x y μ τ two three odd no3 co norm
  have power (g : G) : (μ g)^(Nat.card G)=1 := by rw [←map_pow,pow_card_eq_one',map_one]
  rcases norm with ⟨a,tx,ty⟩|⟨_,b,tx,ty⟩
  · have ne : μ x≠1 := fun e => a (by simp [e])
    exact (fieldCore_inverse SC d3 x y μ τ co ne tx ty _ odd no3 two three (power x) (power y)).imp id
      (fieldBadToBad _ _)
  · have ne : μ y≠1 := fun e => b (by simp [e])
    exact (fieldCore_inverse SC d3 y x μ τ co ne ty tx _ odd no3 two three (power y) (power x)).imp
      swap_long (fun bad => fieldBadToBad _ _ (field_bad_flip _ _ bad))

end RibbonD3Finite
#print axioms RibbonD3Finite.field_from_inverse
