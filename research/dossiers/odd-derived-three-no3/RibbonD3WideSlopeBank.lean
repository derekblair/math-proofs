import RibbonD3WideSlopeGeom0
import RibbonD3WideSlopeGeom1
import RibbonD3WideSlopeGeom2
import RibbonD3WideSlopeGeom3
import RibbonD3WideSlopeGeom4
import RibbonD3WideSlopeGeom5
import RibbonD3WideSlopeGeom6
import RibbonD3WideSlopeGeom7
import RibbonD3WideSlopeGeom8
import RibbonD3WideSlopeGeom9
namespace RibbonD3Wide
open RibbonD3Field
structure GoodGeometry where
  entry : GeometryEntry
  valid : GeomValid entry.geom entry.u entry.v
def goodBank : Array GoodGeometry := #[⟨g0,g0_valid⟩,⟨g1,g1_valid⟩,⟨g2,g2_valid⟩,⟨g3,g3_valid⟩,⟨g4,g4_valid⟩,⟨g5,g5_valid⟩,⟨g6,g6_valid⟩,⟨g7,g7_valid⟩,⟨g8,g8_valid⟩,⟨g9,g9_valid⟩,⟨g10,g10_valid⟩,⟨g11,g11_valid⟩,⟨g12,g12_valid⟩,⟨g13,g13_valid⟩,⟨g14,g14_valid⟩,⟨g15,g15_valid⟩,⟨g16,g16_valid⟩,⟨g17,g17_valid⟩,⟨g18,g18_valid⟩,⟨g19,g19_valid⟩,⟨g20,g20_valid⟩,⟨g21,g21_valid⟩,⟨g22,g22_valid⟩,⟨g23,g23_valid⟩,⟨g24,g24_valid⟩,⟨g25,g25_valid⟩,⟨g26,g26_valid⟩,⟨g27,g27_valid⟩,⟨g28,g28_valid⟩,⟨g29,g29_valid⟩,⟨g30,g30_valid⟩,⟨g31,g31_valid⟩,⟨g32,g32_valid⟩,⟨g33,g33_valid⟩,⟨g34,g34_valid⟩,⟨g35,g35_valid⟩,⟨g36,g36_valid⟩,⟨g37,g37_valid⟩]
def bank : Array GeometryEntry := goodBank.map GoodGeometry.entry
theorem bank_valid : BankValid bank := by
  intro i
  have h : i.val<goodBank.size := by simpa [bank] using i.isLt
  change GeomValid (goodBank.map GoodGeometry.entry)[i.val].geom
    (goodBank.map GoodGeometry.entry)[i.val].u (goodBank.map GoodGeometry.entry)[i.val].v
  simpa only [Array.getElem_map] using goodBank[i.val].valid
end RibbonD3Wide
