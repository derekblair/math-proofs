import Ribbon6Chart
namespace Ribbon6
open HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem adj_inv_left (x y : G) (u v : Bool × G) :
    Ribbon.Adj x⁻¹ y u v ↔ Ribbon.Adj x y u v := by
  unfold Ribbon.Adj
  have p : u.2*x⁻¹=v.2 ↔ v.2*x=u.2 := by
    constructor <;> intro h
    · rw [←h,mul_assoc,inv_mul_cancel,mul_one]
    · rw [← h,mul_assoc,mul_inv_cancel,mul_one]
  have q : v.2*x⁻¹=u.2 ↔ u.2*x=v.2 := by
    constructor <;> intro h
    · rw [←h,mul_assoc,inv_mul_cancel,mul_one]
    · rw [← h,mul_assoc,mul_inv_cancel,mul_one]
  rw [p,q]
  tauto

theorem cycle_inv_left {n : Nat} (x y : G) :
    Ribbon.Cycle x⁻¹ y n ↔ Ribbon.Cycle x y n := by
  constructor <;> rintro ⟨f,hF,adj⟩ <;> refine ⟨f,hF,?_⟩
  · intro i
    exact (adj_inv_left x y _ _).mp (adj i)
  · intro i
    exact (adj_inv_left x y _ _).mpr (adj i)

theorem invert_Hall (x y : G)
    (hu : ∀ t : G, Commute (portU x y) t) (hv : ∀ t : G, Commute (portV x y) t) :
    portC x⁻¹ y = (portC x y)⁻¹ * portU x y ∧
    portU x⁻¹ y = portU x y ∧ portV x⁻¹ y = (portV x y)⁻¹ := by
  let c := portC x y
  let u := portU x y
  let v := portV x y
  have e : portC x⁻¹ y=c⁻¹*u := by
    unfold portC
    rw [inv_inv]
    have p : ⁅x,y⁻¹⁆ = x*c⁻¹*x⁻¹ := by
      simp only [c,portC,commutatorElement_def]; group
    rw [p]
    simp only [u,portU,←show c=portC x y from rfl,commutatorElement_def]
    group
  refine ⟨e,?_,?_⟩
  · change ⁅portC x⁻¹ y,x⁻¹⁆=u
    rw [e,commutatorElement_mul_left_eq_conj_mul,(hu x⁻¹).commutator_eq,
      mul_one,mul_inv_cancel,one_mul,commutatorElement_inv_right,
      commutatorElement_inv_right]
    change x⁻¹*(c⁻¹*u*c)*x=u
    rw [(hu c⁻¹).symm.eq,mul_assoc u,inv_mul_cancel,mul_one,
      (hu x⁻¹).symm.eq]
    simp only [mul_assoc,inv_mul_cancel,mul_one]
    rfl
  · change ⁅portC x⁻¹ y,y⁆=v⁻¹
    rw [e,commutatorElement_mul_left_eq_conj_mul,(hu y).commutator_eq,
      mul_one,mul_inv_cancel,one_mul,commutatorElement_inv_left,
      ←commutatorElement_inv]
    change c⁻¹*v⁻¹*c=v⁻¹
    rw [(hv c⁻¹).inv_left.symm.eq,mul_assoc v⁻¹,inv_mul_cancel,mul_one]

theorem invert_cube (x y : G) (hu : ∀ t : G, Commute (portU x y) t)
    (hv : ∀ t : G, Commute (portV x y) t) (hu3 : (portU x y)^3=1) :
    (portC x⁻¹ y)^3 = ((portC x y)^3)⁻¹ := by
  rw [(invert_Hall x y hu hv).1,((hu (portC x y)⁻¹).symm).mul_pow,hu3,mul_one,inv_pow]

end Ribbon6
