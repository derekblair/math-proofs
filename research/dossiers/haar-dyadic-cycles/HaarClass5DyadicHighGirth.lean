import HaarClass5Commute
import HaarShortClosedIsCycle

namespace HaarClass5DyadicHighGirth
open HaarAllNoncommuting HaarUniversal36 HaarClass5Commute HaarHalfCollision
open scoped commutatorElement
variable {G : Type*} [Group G]

def p (x y : G) : G := x⁻¹*x⁻¹ * ⁅⁅x,y⁆,y⁆⁻¹ * (x⁻¹*x⁻¹)⁻¹
def q (x y : G) : G := y*x⁻¹*y * ⁅⁅x,y⁻¹⁆,x⁻¹⁆⁻¹ * (y*x⁻¹*y)⁻¹

theorem p_mem (x y : G) : p x y ∈ L G 2 := by
  unfold p
  apply (inferInstance : (L G 2).Normal).conj_mem
  exact (L G 2).inv_mem (next (next (Subgroup.mem_top x) y) y) 

theorem pq_commute (nil : L G 5=⊥) (x y : G) : Commute (p x y) (q x y) :=
  centralizes_conj_inverse_triple nil (p_mem x y) x y⁻¹ x⁻¹ (y*x⁻¹*y)

def w64 : List (Fin 3) :=
  [0,1,0,1,2,0,1,0,2,1,0,2,1,2,1,0,2,1,0,1,2,0,1,2,1,0,2,1,0,2,1,2,0,1,2,1,2,0,1,2,0,1,0,2,1,0,1,0,2,1,2,0,1,2,0,1,2,1,0,2,1,0,1,2]

theorem w64_value (x y : G) : prodFrom x y 0 w64 = ⁅p x y,q x y⁆ := by
  norm_num [w64,prodFrom,signPort,port,p,q,commutatorElement_def]
  group

theorem w64_closes (nil : L G 5=⊥) (x y : G) : prodFrom x y 0 w64 = 1 := by
  rw [w64_value,(pq_commute nil x y).commutator_eq]

theorem highGirth_has64 (nil : L G 5=⊥) (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (below : ∀ k, 4≤k → k<34 → Even k → ¬HasCycle x y k) : HasCycle x y 64 := by
  have hc := HaarShortClosedIsCycle.fromWord x y hx hy hxy w64 (by decide) (by decide)
    (by decide) (w64_closes nil x y) (by decide) 34 (by decide) below
  exact hc

end HaarClass5DyadicHighGirth
#print axioms HaarClass5DyadicHighGirth.highGirth_has64
