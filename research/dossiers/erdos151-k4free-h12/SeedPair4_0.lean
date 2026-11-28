import BranchCore

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_4_8 : rowKids 4 8=false := by decide +kernel
theorem pair_4_9 : rowKids 4 9=false := by decide +kernel
end Erdos151Ramsey.Seed53
