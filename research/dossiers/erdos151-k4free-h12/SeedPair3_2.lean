import BranchCore

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_3_9 : rowKids 3 9=false := by decide +kernel
theorem pair_3_11 : rowKids 3 11=false := by decide +kernel
theorem pair_3_12 : rowKids 3 12=false := by decide +kernel
end Erdos151Ramsey.Seed53
