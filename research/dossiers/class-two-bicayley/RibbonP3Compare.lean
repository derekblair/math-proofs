import HaarCycle
import Mathlib.GroupTheory.OrderOfElement

namespace RibbonP3
variable {G : Type*} [Group G]

/-- In the class-two quotient, normal-form equality forces the two abelian
coordinates to match modulo three; no power premise on x or y is needed. -/
theorem abelian_residues (x y c : G) (cx : Commute c x) (cy : Commute c y)
    (hxy : x*y=y*x*c) (ord : orderOf c=3)
    (p q : HaarCycle.Coord) (eq : HaarCycle.norm x y c p=HaarCycle.norm x y c q) :
    p.1%3=q.1%3 ∧ p.2.1%3=q.2.1%3 := by
  have detects (i j : ℤ) (e : c^i=c^j) : i%3=j%3 := by
    have z : c^(i-j)=1 := by rw [zpow_sub,e,mul_inv_cancel]
    have hz := orderOf_dvd_iff_zpow_eq_one.mpr z
    rw [ord] at hz
    exact (Int.modEq_iff_dvd.mpr hz).symm
  constructor
  · apply detects
    apply mul_left_cancel (a:=y*HaarCycle.norm x y c p)
    rw [← HaarCycle.normShiftY x y c cx cy hxy p, eq,
      HaarCycle.normShiftY x y c cx cy hxy q]
  · have hn : (-p.2.1)%3=(-q.2.1)%3 := by
      apply detects
      apply mul_left_cancel (a:=x*HaarCycle.norm x y c p)
      rw [← HaarCycle.normShiftX x y c cx cy hxy p,eq,
        HaarCycle.normShiftX x y c cx cy hxy q]
    omega

/-- Once the integer abelian coordinates agree, cancel them in the
class-two quotient to recover the exact commutator residue. -/
theorem commutator_residue (x y c : G) (ord : orderOf c=3)
    (i j k l : ℤ) (e : HaarCycle.norm x y c (i,j,k)=HaarCycle.norm x y c (i,j,l)) :
    k%3=l%3 := by
  have e' : c^k=c^l := mul_left_cancel e
  have z : c^(k-l)=1 := by rw [zpow_sub,e',mul_inv_cancel]
  have hz := orderOf_dvd_iff_zpow_eq_one.mpr z
  rw [ord] at hz
  exact (Int.modEq_iff_dvd.mpr hz).symm

end RibbonP3
#print axioms RibbonP3.abelian_residues
