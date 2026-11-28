import BranchCore

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_2_8 : rowKids 2 8=false := by decide +kernel
theorem pair_2_11 : rowKids 2 11=false := by decide +kernel
end Erdos151Ramsey.Seed53
