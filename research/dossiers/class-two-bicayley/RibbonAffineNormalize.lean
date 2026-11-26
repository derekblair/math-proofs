import RibbonAffineCocycle

namespace RibbonAffine
open HaarClass4Ports
variable {G K : Type*} [Group G] [Field K]

def IsCocycle (μ : G →* Kˣ) (τ : G → K) : Prop :=
  τ 1=0 ∧ ∀ g h, τ (g*h)=τ g+(μ g : K)*τ h

theorem displacement_cocycle (μ : G →* Kˣ) (ell : D G →* Multiplicative K)
    (e : Equivariant μ ell) (s : G) : IsCocycle μ (displacement ell s) := by
  refine ⟨?_,displacement_mul μ ell e s⟩
  have E : cAt 1 s = 1 := Subtype.ext (by simp [cAt])
  unfold displacement
  rw [E,map_one]
  rfl

private theorem zero_inv {μ : G →* Kˣ} {τ : G → K} (co : IsCocycle μ τ)
    {g : G} (h : τ g=0) : τ g⁻¹=0 := by
  have H := co.2 g g⁻¹
  rw [mul_inv_cancel,co.1,h,zero_add] at H
  exact (mul_eq_zero.mp H.symm).resolve_left (Units.ne_zero _)

private theorem zero_comm {μ : G →* Kˣ} {τ : G → K} (co : IsCocycle μ τ)
    {x y : G} (hx : τ x=0) (hy : τ y=0) : τ (portC x y)=0 := by
  simp only [portC,commutatorElement_def,inv_inv,co.2,hx,hy,
    zero_inv co hx,zero_inv co hy,mul_zero,add_zero]

private theorem shift_co {μ : G →* Kˣ} {τ : G → K} (co : IsCocycle μ τ) (v : K) :
    IsCocycle μ (fun g => τ g+((μ g:K)-1)*v) := by
  constructor
  · simp [co.1]
  · intro g h
    dsimp
    rw [co.2,map_mul,Units.val_mul]
    ring

private theorem scale_co {μ : G →* Kˣ} {τ : G → K} (co : IsCocycle μ τ) (k : K) :
    IsCocycle μ (fun g => k*τ g) := by
  constructor
  · simp [co.1]
  · intro g h
    dsimp
    rw [co.2]
    ring

theorem unit_kills_derived (μ : G →* Kˣ) (d : D G) : μ d.val=1 :=
  Abelianization.commutator_subset_ker μ (show d.val∈commutator G from d.property)

theorem normalized {μ : G →* Kˣ} {τ : G → K} (co : IsCocycle μ τ) (x y : G)
    (hx : μ x≠1) (hc : τ (portC x y)≠0) :
    ∃ σ : G → K, IsCocycle μ σ ∧ σ x=0 ∧ σ y=1 := by
  have hxd : (1:K) - (μ x:K) ≠ 0 := by
    intro E
    apply hx
    exact Units.ext (sub_eq_zero.mp E).symm
  let v := τ x / ((1:K)-(μ x:K))
  let d : G → K := fun g => τ g + ((μ g:K)-1)*v
  have coD := shift_co co v
  have Dx : d x=0 := by
    dsimp [d,v]
    field_simp
    ring
  have C0 : d (portC x y) ≠ 0 := by
    have H := unit_kills_derived μ ⟨portC x y,layer_c x y⟩
    change μ (portC x y)=1 at H
    simpa [d,H] using hc
  have Dy : d y≠0 := fun e => C0 (zero_comm coD Dx e)
  refine ⟨fun g => (d y)⁻¹*d g,scale_co coD _,by simp [Dx],?_⟩
  exact inv_mul_cancel₀ Dy

end RibbonAffine
#print axioms RibbonAffine.normalized
