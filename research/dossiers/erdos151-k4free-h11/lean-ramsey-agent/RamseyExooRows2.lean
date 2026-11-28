import RamseyExooCore

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_2 : rowCheck 2 = false := by decide +kernel
theorem tri_2 : tfCheck 2 = true := by decide +kernel
theorem bound_3 : rowCheck 3 = false := by decide +kernel
theorem tri_3 : tfCheck 3 = true := by decide +kernel
end Erdos151Ramsey.Exoo
