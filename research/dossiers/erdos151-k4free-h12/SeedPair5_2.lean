import BranchCore

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_5_9 : rowKids 5 9=false := by decide +kernel
theorem pair_5_11 : rowKids 5 11=false := by decide +kernel
end Erdos151Ramsey.Seed53
