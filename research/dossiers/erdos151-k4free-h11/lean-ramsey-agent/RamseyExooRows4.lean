import RamseyExooCore

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_6 : rowCheck 6 = false := by decide +kernel
theorem tri_6 : tfCheck 6 = true := by decide +kernel
theorem bound_7 : rowCheck 7 = false := by decide +kernel
theorem tri_7 : tfCheck 7 = true := by decide +kernel
theorem bound_8 : rowCheck 8 = false := by decide +kernel
theorem tri_8 : tfCheck 8 = true := by decide +kernel
end Erdos151Ramsey.Exoo
