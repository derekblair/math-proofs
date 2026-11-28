import BranchCore
import SeedTrio2_3
import SeedTrio2_4
import SeedTrio2_6
import SeedTrio2_7
import SeedTrio2_10
import SeedPair2_0
import SeedPair2_1
import SeedPair2_2
import SeedPair2_3

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_2_0 : rowKids 2 0=false := by decide +kernel
theorem pair_2_1 : rowKids 2 1=false := by decide +kernel
theorem pair_2_2 : rowKids 2 2=false := by decide +kernel
theorem pair_2_9 : rowKids 2 9=false := by decide +kernel
theorem pair_2_12 : rowKids 2 12=false := by decide +kernel
theorem pair_2_14 : rowKids 2 14=false := by decide +kernel
theorem pair_2_22 : rowKids 2 22=false := by decide +kernel
theorem pair_2_23 : rowKids 2 23=false := by decide +kernel
theorem pair_2_24 : rowKids 2 24=false := by decide +kernel
theorem pair_2_25 : rowKids 2 25=false := by decide +kernel
theorem pair_2_27 : rowKids 2 27=false := by decide +kernel
theorem pair_2_28 : rowKids 2 28=false := by decide +kernel
theorem pair_2_31 : rowKids 2 31=false := by decide +kernel
theorem pair_2_39 : rowKids 2 39=false := by decide +kernel
theorem pair_2_40 : rowKids 2 40=false := by decide +kernel
theorem pair_2_41 : rowKids 2 41=false := by decide +kernel
theorem pair_2_42 : rowKids 2 42=false := by decide +kernel
theorem pair_2_43 : rowKids 2 43=false := by decide +kernel
theorem pair_2_44 : rowKids 2 44=false := by decide +kernel
theorem pair_2_45 : rowKids 2 45=false := by decide +kernel
theorem pair_2_46 : rowKids 2 46=false := by decide +kernel
theorem pair_2_47 : rowKids 2 47=false := by decide +kernel
theorem pair_2_48 : rowKids 2 48=false := by decide +kernel
theorem pair_2_49 : rowKids 2 49=false := by decide +kernel
theorem pair_2_50 : rowKids 2 50=false := by decide +kernel
theorem pair_2_51 : rowKids 2 51=false := by decide +kernel
theorem bound_2 : rowCheck 2=false := row_of_kids 2 (fun b=>Fin.cases pair_2_0 ( Fin.cases pair_2_1 ( Fin.cases pair_2_2 ( Fin.cases pair_2_3 ( Fin.cases pair_2_4 ( Fin.cases pair_2_5 ( Fin.cases pair_2_6 ( Fin.cases pair_2_7 ( Fin.cases pair_2_8 ( Fin.cases pair_2_9 ( Fin.cases pair_2_10 ( Fin.cases pair_2_11 ( Fin.cases pair_2_12 ( Fin.cases pair_2_13 ( Fin.cases pair_2_14 ( Fin.cases pair_2_15 ( Fin.cases pair_2_16 ( Fin.cases pair_2_17 ( Fin.cases pair_2_18 ( Fin.cases pair_2_19 ( Fin.cases pair_2_20 ( Fin.cases pair_2_21 ( Fin.cases pair_2_22 ( Fin.cases pair_2_23 ( Fin.cases pair_2_24 ( Fin.cases pair_2_25 ( Fin.cases pair_2_26 ( Fin.cases pair_2_27 ( Fin.cases pair_2_28 ( Fin.cases pair_2_29 ( Fin.cases pair_2_30 ( Fin.cases pair_2_31 ( Fin.cases pair_2_32 ( Fin.cases pair_2_33 ( Fin.cases pair_2_34 ( Fin.cases pair_2_35 ( Fin.cases pair_2_36 ( Fin.cases pair_2_37 ( Fin.cases pair_2_38 ( Fin.cases pair_2_39 ( Fin.cases pair_2_40 ( Fin.cases pair_2_41 ( Fin.cases pair_2_42 ( Fin.cases pair_2_43 ( Fin.cases pair_2_44 ( Fin.cases pair_2_45 ( Fin.cases pair_2_46 ( Fin.cases pair_2_47 ( Fin.cases pair_2_48 ( Fin.cases pair_2_49 ( Fin.cases pair_2_50 (Fin.cases pair_2_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_2 : tfCheck 2=true := by decide +kernel
end Erdos151Ramsey.Seed53
