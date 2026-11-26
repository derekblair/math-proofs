import RibbonOddInterfaces
import RibbonStationaryChart
import Ribbon6Invert

namespace RibbonD3Orientation
open RibbonStationaryChart
variable {G K R : Type*} [Group G] [Field K] [CommRing R]

def gap (μ : G→*Rˣ) (τ : G→R) (x y : G) : R :=
  (1-(μ x:R))*τ y-(1-(μ y:R))*τ x

theorem gap_swap (μ : G→*Rˣ) (τ : G→R) (x y : G) :
    gap μ τ y x = -gap μ τ x y := by unfold gap; ring

theorem gap_inv_left (μ : G→*Rˣ) (τ : G→R) (co : Aff μ τ) (x y : G) :
    gap μ τ x⁻¹ y = -(↑(μ x)⁻¹:R)*gap μ τ x y := by
  unfold gap
  rw [inv_sound μ τ co,map_inv]
  have e : (↑(μ x)⁻¹:R)*(μ x:R)=1 := Units.inv_mul (μ x)
  linear_combination -τ y * e

theorem gap_inv_right (μ : G→*Rˣ) (τ : G→R) (co : Aff μ τ) (x y : G) :
    gap μ τ x y⁻¹ = -(↑(μ y)⁻¹:R)*gap μ τ x y := by
  calc
    _ = -gap μ τ y⁻¹ x := by rw [gap_swap]
    _ = _ := by rw [gap_inv_left μ τ co,gap_swap μ τ y x] <;> ring

theorem gap_unit (f : R→+*K) (lift : ∀ r, f r≠0→IsUnit r)
    (μ : G→*Rˣ) (τ : G→R) (x y : G)
    (n : RibbonP11.Normalized f x y μ τ) : IsUnit (gap μ τ x y) := by
  rcases n with ⟨a,tx,ty⟩ | ⟨a,b,tx,ty⟩
  · unfold gap
    rw [tx,ty,mul_one,mul_zero,sub_zero]
    apply lift
    intro h
    rw [map_sub,map_one,sub_eq_zero] at h
    exact a h.symm
  · unfold gap
    rw [tx,ty,mul_zero,mul_one,zero_sub]
    apply IsUnit.neg
    apply lift
    intro h
    rw [map_sub,map_one,sub_eq_zero] at h
    exact b h.symm

theorem shift_affine (μ : G→*Rˣ) (τ : G→R) (co : Aff μ τ) (c d : R) :
    Aff μ (fun g => d*(τ g-c*(1-(μ g:R)))) := by
  refine ⟨by simp [co.1],?_⟩
  intro x y
  dsimp only
  rw [co.2,map_mul,Units.val_mul]
  ring

theorem pivot_x (f : R→+*K) (lift : ∀ r, f r≠0→IsUnit r)
    (μ : G→*Rˣ) (τ : G→R) (co : Aff μ τ) (x y : G)
    (p : f (μ x:R)≠1) (unitGap : IsUnit (gap μ τ x y)) :
    ∃ σ : G→R, Aff μ σ ∧ σ x=0 ∧ σ y=1 := by
  have H : IsUnit (1-(μ x:R)) := lift _ (fun z => p (by
    rw [map_sub,map_one,sub_eq_zero] at z
    exact z.symm))
  obtain ⟨a,ha⟩ := H
  let c : R := τ x*(a⁻¹:Rˣ)
  have cancel : (↑a⁻¹:R)*(1-(μ x:R))=1 := by
    rw [←ha,←Units.val_mul,inv_mul_cancel,Units.val_one]
  have E : τ y-c*(1-(μ y:R)) = (↑a⁻¹:R)*gap μ τ x y := by
    unfold gap c
    linear_combination -τ y * cancel
  have F : IsUnit (τ y-c*(1-(μ y:R))) := E ▸ (a⁻¹).isUnit.mul unitGap
  obtain ⟨b,hb⟩ := F
  refine ⟨fun g => (↑b⁻¹:R)*(τ g-c*(1-(μ g:R))),shift_affine μ τ co c ↑b⁻¹,?_,?_⟩
  · change (↑b⁻¹:R)*(τ x-c*(1-(μ x:R)))=0
    unfold c
    rw [mul_assoc (τ x),cancel,mul_one,sub_self,mul_zero]
  · change (↑b⁻¹:R)*(τ y-c*(1-(μ y:R)))=1
    rw [←hb,←Units.val_mul,inv_mul_cancel,Units.val_one]

theorem renormalize (f : R→+*K) (lift : ∀ r, f r≠0→IsUnit r)
    (μ : G→*Rˣ) (τ : G→R) (co : Aff μ τ) (x y : G)
    (unitGap : IsUnit (gap μ τ x y)) :
    ∃ σ : G→R, Aff μ σ ∧ RibbonP11.Normalized f x y μ σ := by
  by_cases hx : f (μ x:R)=1
  · have hy : f (μ y:R)≠1 := by
      intro h
      have E : f (gap μ τ x y)=0 := by simp [gap,hx,h]
      exact (unitGap.map f).ne_zero E
    obtain ⟨σ,C,ty,tx⟩ := pivot_x f lift μ τ co y x hy
      (by rw [gap_swap]; exact unitGap.neg)
    exact ⟨σ,C,Or.inr ⟨hx,hy,tx,ty⟩⟩
  · obtain ⟨σ,C,tx,ty⟩ := pivot_x f lift μ τ co x y hx unitGap
    exact ⟨σ,C,Or.inl ⟨hx,tx,ty⟩⟩

structure Motion where
  ix : Bool
  iy : Bool
  swap : Bool
  deriving DecidableEq

def motionPow (x : G) (keep : Bool) : G := if keep then x else x⁻¹

def act (m : Motion) (x y : G) : G×G :=
  let a := motionPow x (!m.ix)
  let b := motionPow y (!m.iy)
  if m.swap then (b,a) else (a,b)

theorem cycle_inv_right {n : Nat} (x y : G) (h : Ribbon.Cycle x y⁻¹ n) :
    Ribbon.Cycle x y n :=
  RibbonP3.flip_cycle ((Ribbon6.cycle_inv_left y x).mp (RibbonP3.flip_cycle h))

theorem cycle_unact {n : Nat} (m : Motion) (x y : G)
    (h : Ribbon.Cycle (act m x y).1 (act m x y).2 n) :
    Ribbon.Cycle x y n := by
  rcases m with ⟨a,b,s⟩
  cases a <;> cases b <;> cases s <;>
    simp [act,motionPow] at h <;>
    first
    | exact h
    | exact RibbonP3.flip_cycle h
    | exact (Ribbon6.cycle_inv_left x y).mp h
    | exact cycle_inv_right x y h
    | exact (Ribbon6.cycle_inv_left x y).mp (RibbonP3.flip_cycle h)
    | exact cycle_inv_right x y (RibbonP3.flip_cycle h)
    | exact (Ribbon6.cycle_inv_left x y).mp (cycle_inv_right x⁻¹ y h)
    | exact (Ribbon6.cycle_inv_left x y).mp (cycle_inv_right x⁻¹ y (RibbonP3.flip_cycle h))

theorem gap_act (m : Motion) (μ : G→*Rˣ) (τ : G→R) (co : Aff μ τ)
    (x y : G) (n : IsUnit (gap μ τ x y)) :
    IsUnit (gap μ τ (act m x y).1 (act m x y).2) := by
  rcases m with ⟨a,b,s⟩
  have aU : IsUnit (-(↑(μ x)⁻¹:R)) := ((μ x)⁻¹).isUnit.neg
  have bU : IsUnit (-(↑(μ y)⁻¹:R)) := ((μ y)⁻¹).isUnit.neg
  cases a <;> cases b <;> cases s <;>
    simp [act,motionPow] <;>
    first
    | exact n
    | rw [gap_swap μ τ x y]; exact n.neg
    | rw [gap_inv_left μ τ co]; exact aU.mul n
    | rw [gap_inv_right μ τ co]; exact bU.mul n
    | rw [gap_swap μ τ x⁻¹ y,gap_inv_left μ τ co]; exact (aU.mul n).neg
    | rw [gap_swap μ τ x y⁻¹,gap_inv_right μ τ co]; exact (bU.mul n).neg
    | rw [gap_inv_left μ τ co,gap_inv_right μ τ co]; exact aU.mul (bU.mul n)
    | rw [gap_swap μ τ x⁻¹ y⁻¹,gap_inv_left μ τ co,gap_inv_right μ τ co]; exact (aU.mul (bU.mul n)).neg

theorem normalize_act (m : Motion) (f : R→+*K) (lift : ∀ r, f r≠0→IsUnit r)
    (μ : G→*Rˣ) (τ : G→R) (co : Aff μ τ) (x y : G)
    (n : RibbonP11.Normalized f x y μ τ) :
    ∃ σ : G→R, Aff μ σ ∧ RibbonP11.Normalized f (act m x y).1 (act m x y).2 μ σ :=
  renormalize f lift μ τ co _ _ (gap_act m μ τ co x y (gap_unit f lift μ τ x y n))

end RibbonD3Orientation
#print axioms RibbonD3Orientation.renormalize

#print axioms RibbonD3Orientation.normalize_act
