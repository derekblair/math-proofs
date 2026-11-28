import BranchCore

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_4_10 : rowKids 4 10=false := by decide +kernel
theorem pair_4_12 : rowKids 4 12=false := by decide +kernel
end Erdos151Ramsey.Seed53
