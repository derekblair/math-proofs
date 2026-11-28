import RamseySeed53Core

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem bound_15 : rowCheck 15=false := by decide +kernel
theorem tri_15 : tfCheck 15=true := by decide +kernel
theorem bound_16 : rowCheck 16=false := by decide +kernel
theorem tri_16 : tfCheck 16=true := by decide +kernel
theorem bound_17 : rowCheck 17=false := by decide +kernel
theorem tri_17 : tfCheck 17=true := by decide +kernel
end Erdos151Ramsey.Seed53
