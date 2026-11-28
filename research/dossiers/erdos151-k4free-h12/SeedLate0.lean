import RamseySeed53Core

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_13 : rowCheck 13=false := by decide +kernel
theorem tri_13 : tfCheck 13=true := by decide +kernel
theorem bound_14 : rowCheck 14=false := by decide +kernel
theorem tri_14 : tfCheck 14=true := by decide +kernel
end Erdos151Ramsey.Seed53
