import RibbonAffineNormalize

namespace RibbonP11
open RibbonAffine HaarClass4Ports
variable {G R : Type*} [Group G] [CommRing R]

def IsCocycle (μ : G →* Rˣ) (τ : G → R) : Prop :=
  τ 1=0 ∧ ∀ g h, τ (g*h)=τ g+(μ g : R)*τ h

def Equivariant (μ : G →* Rˣ) (ell : D G →* Multiplicative R) : Prop :=
  ∀ (g : G) (d : D G),
    Multiplicative.toAdd (ell (MulAut.conjNormal g d)) =
      (μ g : R)*Multiplicative.toAdd (ell d)

def disp (ell : D G →* Multiplicative R) (s g : G) : R :=
  Multiplicative.toAdd (ell (cAt g s))

open scoped commutatorElement in
theorem disp_co (μ : G →* Rˣ) (ell : D G →* Multiplicative R)
    (e : Equivariant μ ell) (s : G) : IsCocycle μ (disp ell s) := by
  constructor
  · have E : cAt 1 s = 1 := Subtype.ext (by simp [cAt])
    unfold disp
    rw [E,map_one]
    rfl
  · intro g h
    have E : cAt (g*h) s = MulAut.conjNormal g (cAt h s)*cAt g s := by
      apply Subtype.ext
      simpa only [cAt,MulAut.conjNormal_apply,Subgroup.coe_mul] using
        commutatorElement_mul_left_eq_conj_mul g h s
    unfold disp
    rw [E,map_mul]
    change Multiplicative.toAdd (ell (MulAut.conjNormal g (cAt h s))) +
      Multiplicative.toAdd (ell (cAt g s)) = _
    rw [e,add_comm]

open scoped commutatorElement in
theorem disp_derived (μ : G →* Rˣ) (ell : D G →* Multiplicative R)
    (e : Equivariant μ ell) (s : G) (d : D G) :
    disp ell s d.val = (1-(μ s:R))*Multiplicative.toAdd (ell d) := by
  have E : cAt d.val s = d*(MulAut.conjNormal s d)⁻¹ := by
    apply Subtype.ext
    simpa only [cAt,MulAut.conjNormal_apply,Subgroup.coe_mul,Subgroup.coe_inv] using
      (show ⁅d.val,s⁆=d.val*(s*d.val*s⁻¹)⁻¹ by rw [commutatorElement_def]; group)
  unfold disp
  rw [E,map_mul,map_inv]
  change Multiplicative.toAdd (ell d) + -(Multiplicative.toAdd (ell (MulAut.conjNormal s d))) = _
  rw [e]
  ring

private theorem shift_co {μ : G →* Rˣ} {τ : G → R} (co : IsCocycle μ τ) (v : R) :
    IsCocycle μ (fun g => τ g+((μ g:R)-1)*v) := by
  constructor
  · simp [co.1]
  · intro g h
    dsimp
    rw [co.2,map_mul,Units.val_mul]
    ring

private theorem scale_co {μ : G →* Rˣ} {τ : G → R} (co : IsCocycle μ τ) (k : R) :
    IsCocycle μ (fun g => k*τ g) := by
  constructor
  · simp [co.1]
  · intro g h
    dsimp
    rw [co.2]
    ring

theorem normalized {μ : G →* Rˣ} {τ : G → R} (co : IsCocycle μ τ) (x y : G)
    (hx : IsUnit (1-(μ x:R))) (hc : IsUnit (τ (portC x y))) :
    ∃ σ : G → R, IsCocycle μ σ ∧ σ x=0 ∧ σ y=1 := by
  obtain ⟨a,ha⟩ := hx
  let v := (↑a⁻¹:R)*τ x
  let d : G → R := fun g => τ g+((μ g:R)-1)*v
  have coD : IsCocycle μ d := shift_co co v
  have Dx : d x=0 := by
    dsimp [d,v]
    rw [show (μ x:R)-1=-(a:R) by rw [ha]; ring,neg_mul,←mul_assoc,Units.mul_inv,one_mul]
    ring
  have C0 : IsUnit (d (portC x y)) := by
    have H : μ (portC x y)=1 := Abelianization.commutator_subset_ker μ
      (show portC x y∈commutator G from layer_c x y)
    simpa [d,H] using hc
  have rel : (μ x:R)*d y = d y + (μ (y*x) : R)*d (portC x y) := by
    have eq := congrArg d (ports_xy x y)
    rw [coD.2 x y,coD.2 (y*x) _,coD.2 y x,Dx,zero_add,mul_zero,add_zero] at eq
    exact eq
  have rel' : (μ (y*x):R)*d (portC x y)=((μ x:R)-1)*d y := by
    rw [sub_mul,one_mul]
    linear_combination -rel
  have Dy : IsUnit (d y) := by
    apply isUnit_of_mul_isUnit_right (x:=(μ x:R)-1)
    rw [←rel']
    exact (μ (y*x)).isUnit.mul C0
  obtain ⟨b,hb⟩ := Dy
  refine ⟨fun g => (↑b⁻¹:R)*d g,scale_co coD _,by simp [Dx],?_⟩
  change (↑b⁻¹:R)*d y=1
  rw [←hb, Units.inv_mul]

end RibbonP11
#print axioms RibbonP11.disp_derived
#print axioms RibbonP11.normalized
