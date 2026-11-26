import RibbonP3Identity
import HaarClass5Commute

namespace RibbonP3
open HaarUniversal36 HaarClass5Commute
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem endpoint_central (nil : L G 5 = ⊥) (x y : G) :
    ∀ g, Commute (trace x y false a) g := by
  let H := ⁅x,y*y⁆
  let D := ⁅x⁻¹,H⁻¹⁆
  have HH : H ∈ L G 1 := next (Subgroup.mem_top x) (y*y)
  have HD : D ∈ L G 2 := by
    have h := next ((L G 1).inv_mem HH) x⁻¹
    change ⁅x⁻¹,H⁻¹⁆ ∈ L G 2
    rw [←commutatorElement_inv]
    exact (L G 2).inv_mem h
  have e : x⁻¹ * H⁻¹ * x = D*H⁻¹ := by dsimp [D]; rw [commutatorElement_def]; group
  have hW : ⁅H,x⁻¹*H⁻¹*x⁆=⁅H,D⁆ := by
    rw [e]
    simp only [commutatorElement_def]
    group
  have hL : ⁅H,D⁆ ∈ L G 4 := by
    rw [←commutatorElement_inv]
    exact (L G 4).inv_mem (comm_delta HD x (y*y))
  have hC (g : G) : Commute ⁅H,D⁆ g := by
    apply commutatorElement_eq_one_iff_commute.mp
    have h := next hL g
    change ⁅⁅H,D⁆,g⁆ ∈ L G 5 at h
    rwa [nil,Subgroup.mem_bot] at h
  have htr : trace x y false a=⁅H,D⁆ := by
    rw [factorA,←show H=⁅x,y*y⁆ from rfl,hW,(hC x).symm.eq]
    simp
  rw [htr]
  exact hC

theorem endpoint_all (nil : L G 5=⊥) (x y : G) :
    trace x y false b=trace x y false a ∧
    trace x y false ax=trace x y false a ∧
    trace x y false bx=trace x y false a := by
  have s (z : G) : z*trace x y false a*z⁻¹=trace x y false a := by
    rw [(endpoint_central nil x y z).symm.eq]
    simp
  exact ⟨(endpoint_b x y).trans (s _),(endpoint_ax x y).trans (s _),(endpoint_bx x y).trans (s _)⟩

end RibbonP3
#print axioms RibbonP3.endpoint_all
