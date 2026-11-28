import RamseyExooCore

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_12 : rowCheck 12 = false := by decide +kernel
theorem tri_12 : tfCheck 12 = true := by decide +kernel
theorem bound_13 : rowCheck 13 = false := by decide +kernel
theorem tri_13 : tfCheck 13 = true := by decide +kernel
theorem bound_14 : rowCheck 14 = false := by decide +kernel
theorem tri_14 : tfCheck 14 = true := by decide +kernel
theorem bound_15 : rowCheck 15 = false := by decide +kernel
theorem tri_15 : tfCheck 15 = true := by decide +kernel
end Erdos151Ramsey.Exoo
