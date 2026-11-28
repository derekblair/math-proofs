import RamseyExooCore

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_9 : rowCheck 9 = false := by decide +kernel
theorem tri_9 : tfCheck 9 = true := by decide +kernel
theorem bound_10 : rowCheck 10 = false := by decide +kernel
theorem tri_10 : tfCheck 10 = true := by decide +kernel
theorem bound_11 : rowCheck 11 = false := by decide +kernel
theorem tri_11 : tfCheck 11 = true := by decide +kernel
end Erdos151Ramsey.Exoo
