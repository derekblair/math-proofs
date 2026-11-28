import BranchCore
import SeedTrio0_1
import SeedTrio0_2
import SeedTrio0_3
import SeedTrio0_4
import SeedTrio0_5
import SeedTrio0_6
import SeedPair0_0
import SeedPair0_1
import SeedPair0_2
import SeedPair0_3
import SeedPair0_4

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_0_0 : rowKids 0 0=false := by decide +kernel
theorem pair_0_7 : rowKids 0 7=false := by decide +kernel
theorem pair_0_10 : rowKids 0 10=false := by decide +kernel
theorem pair_0_23 : rowKids 0 23=false := by decide +kernel
theorem pair_0_25 : rowKids 0 25=false := by decide +kernel
theorem pair_0_26 : rowKids 0 26=false := by decide +kernel
theorem pair_0_27 : rowKids 0 27=false := by decide +kernel
theorem pair_0_31 : rowKids 0 31=false := by decide +kernel
theorem pair_0_35 : rowKids 0 35=false := by decide +kernel
theorem pair_0_39 : rowKids 0 39=false := by decide +kernel
theorem pair_0_40 : rowKids 0 40=false := by decide +kernel
theorem pair_0_41 : rowKids 0 41=false := by decide +kernel
theorem pair_0_42 : rowKids 0 42=false := by decide +kernel
theorem pair_0_43 : rowKids 0 43=false := by decide +kernel
theorem pair_0_44 : rowKids 0 44=false := by decide +kernel
theorem pair_0_45 : rowKids 0 45=false := by decide +kernel
theorem pair_0_46 : rowKids 0 46=false := by decide +kernel
theorem pair_0_47 : rowKids 0 47=false := by decide +kernel
theorem pair_0_48 : rowKids 0 48=false := by decide +kernel
theorem pair_0_49 : rowKids 0 49=false := by decide +kernel
theorem pair_0_50 : rowKids 0 50=false := by decide +kernel
theorem pair_0_51 : rowKids 0 51=false := by decide +kernel
theorem bound_0 : rowCheck 0=false := row_of_kids 0 (fun b=>Fin.cases pair_0_0 ( Fin.cases pair_0_1 ( Fin.cases pair_0_2 ( Fin.cases pair_0_3 ( Fin.cases pair_0_4 ( Fin.cases pair_0_5 ( Fin.cases pair_0_6 ( Fin.cases pair_0_7 ( Fin.cases pair_0_8 ( Fin.cases pair_0_9 ( Fin.cases pair_0_10 ( Fin.cases pair_0_11 ( Fin.cases pair_0_12 ( Fin.cases pair_0_13 ( Fin.cases pair_0_14 ( Fin.cases pair_0_15 ( Fin.cases pair_0_16 ( Fin.cases pair_0_17 ( Fin.cases pair_0_18 ( Fin.cases pair_0_19 ( Fin.cases pair_0_20 ( Fin.cases pair_0_21 ( Fin.cases pair_0_22 ( Fin.cases pair_0_23 ( Fin.cases pair_0_24 ( Fin.cases pair_0_25 ( Fin.cases pair_0_26 ( Fin.cases pair_0_27 ( Fin.cases pair_0_28 ( Fin.cases pair_0_29 ( Fin.cases pair_0_30 ( Fin.cases pair_0_31 ( Fin.cases pair_0_32 ( Fin.cases pair_0_33 ( Fin.cases pair_0_34 ( Fin.cases pair_0_35 ( Fin.cases pair_0_36 ( Fin.cases pair_0_37 ( Fin.cases pair_0_38 ( Fin.cases pair_0_39 ( Fin.cases pair_0_40 ( Fin.cases pair_0_41 ( Fin.cases pair_0_42 ( Fin.cases pair_0_43 ( Fin.cases pair_0_44 ( Fin.cases pair_0_45 ( Fin.cases pair_0_46 ( Fin.cases pair_0_47 ( Fin.cases pair_0_48 ( Fin.cases pair_0_49 ( Fin.cases pair_0_50 (Fin.cases pair_0_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_0 : tfCheck 0=true := by decide +kernel
end Erdos151Ramsey.Seed53
