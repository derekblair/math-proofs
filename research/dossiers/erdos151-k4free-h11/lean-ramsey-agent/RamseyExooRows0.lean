import RamseyExooCore

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_0 : rowCheck 0 = false := by decide +kernel
theorem tri_0 : tfCheck 0 = true := by decide +kernel
end Erdos151Ramsey.Exoo
