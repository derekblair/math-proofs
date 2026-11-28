import BranchCore

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_3_6 : rowKids 3 6=false := by decide +kernel
theorem pair_3_8 : rowKids 3 8=false := by decide +kernel
end Erdos151Ramsey.Seed53
