import BK73LB4Core
import BK73Sound1
namespace BK73
/-- all 2^10 orientations of F?qvo fail diameter ≤ 4 (kernel-checked) -/
theorem lb4_top : allL lbp4 10 10 [] = true := by decide +kernel
end BK73
