import BranchCore
import SeedTrio1_2
import SeedTrio1_3
import SeedTrio1_4
import SeedTrio1_5
import SeedTrio1_6
import SeedTrio1_10
import SeedPair1_0
import SeedPair1_1
import SeedPair1_2
import SeedPair1_3

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_1_0 : rowKids 1 0=false := by decide +kernel
theorem pair_1_1 : rowKids 1 1=false := by decide +kernel
theorem pair_1_8 : rowKids 1 8=false := by decide +kernel
theorem pair_1_13 : rowKids 1 13=false := by decide +kernel
theorem pair_1_21 : rowKids 1 21=false := by decide +kernel
theorem pair_1_22 : rowKids 1 22=false := by decide +kernel
theorem pair_1_24 : rowKids 1 24=false := by decide +kernel
theorem pair_1_26 : rowKids 1 26=false := by decide +kernel
theorem pair_1_27 : rowKids 1 27=false := by decide +kernel
theorem pair_1_32 : rowKids 1 32=false := by decide +kernel
theorem pair_1_38 : rowKids 1 38=false := by decide +kernel
theorem pair_1_39 : rowKids 1 39=false := by decide +kernel
theorem pair_1_40 : rowKids 1 40=false := by decide +kernel
theorem pair_1_41 : rowKids 1 41=false := by decide +kernel
theorem pair_1_42 : rowKids 1 42=false := by decide +kernel
theorem pair_1_43 : rowKids 1 43=false := by decide +kernel
theorem pair_1_44 : rowKids 1 44=false := by decide +kernel
theorem pair_1_45 : rowKids 1 45=false := by decide +kernel
theorem pair_1_46 : rowKids 1 46=false := by decide +kernel
theorem pair_1_47 : rowKids 1 47=false := by decide +kernel
theorem pair_1_48 : rowKids 1 48=false := by decide +kernel
theorem pair_1_49 : rowKids 1 49=false := by decide +kernel
theorem pair_1_50 : rowKids 1 50=false := by decide +kernel
theorem pair_1_51 : rowKids 1 51=false := by decide +kernel
theorem bound_1 : rowCheck 1=false := row_of_kids 1 (fun b=>Fin.cases pair_1_0 ( Fin.cases pair_1_1 ( Fin.cases pair_1_2 ( Fin.cases pair_1_3 ( Fin.cases pair_1_4 ( Fin.cases pair_1_5 ( Fin.cases pair_1_6 ( Fin.cases pair_1_7 ( Fin.cases pair_1_8 ( Fin.cases pair_1_9 ( Fin.cases pair_1_10 ( Fin.cases pair_1_11 ( Fin.cases pair_1_12 ( Fin.cases pair_1_13 ( Fin.cases pair_1_14 ( Fin.cases pair_1_15 ( Fin.cases pair_1_16 ( Fin.cases pair_1_17 ( Fin.cases pair_1_18 ( Fin.cases pair_1_19 ( Fin.cases pair_1_20 ( Fin.cases pair_1_21 ( Fin.cases pair_1_22 ( Fin.cases pair_1_23 ( Fin.cases pair_1_24 ( Fin.cases pair_1_25 ( Fin.cases pair_1_26 ( Fin.cases pair_1_27 ( Fin.cases pair_1_28 ( Fin.cases pair_1_29 ( Fin.cases pair_1_30 ( Fin.cases pair_1_31 ( Fin.cases pair_1_32 ( Fin.cases pair_1_33 ( Fin.cases pair_1_34 ( Fin.cases pair_1_35 ( Fin.cases pair_1_36 ( Fin.cases pair_1_37 ( Fin.cases pair_1_38 ( Fin.cases pair_1_39 ( Fin.cases pair_1_40 ( Fin.cases pair_1_41 ( Fin.cases pair_1_42 ( Fin.cases pair_1_43 ( Fin.cases pair_1_44 ( Fin.cases pair_1_45 ( Fin.cases pair_1_46 ( Fin.cases pair_1_47 ( Fin.cases pair_1_48 ( Fin.cases pair_1_49 ( Fin.cases pair_1_50 (Fin.cases pair_1_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_1 : tfCheck 1=true := by decide +kernel
end Erdos151Ramsey.Seed53
