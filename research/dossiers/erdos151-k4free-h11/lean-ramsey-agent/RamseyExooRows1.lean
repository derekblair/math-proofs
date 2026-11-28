import RamseyExooCore

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_1 : rowCheck 1 = false := by decide +kernel
theorem tri_1 : tfCheck 1 = true := by decide +kernel
end Erdos151Ramsey.Exoo
