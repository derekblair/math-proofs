import RamseyExooCore

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_4 : rowCheck 4 = false := by decide +kernel
theorem tri_4 : tfCheck 4 = true := by decide +kernel
theorem bound_5 : rowCheck 5 = false := by decide +kernel
theorem tri_5 : tfCheck 5 = true := by decide +kernel
end Erdos151Ramsey.Exoo
