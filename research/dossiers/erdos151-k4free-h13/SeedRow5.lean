import BranchCore
import SeedTrio5_7
import SeedPair5_0
import SeedPair5_1
import SeedPair5_2
import SeedPair5_3
import SeedPair5_4

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_5_0 : rowKids 5 0=false := by decide +kernel
theorem pair_5_1 : rowKids 5 1=false := by decide +kernel
theorem pair_5_2 : rowKids 5 2=false := by decide +kernel
theorem pair_5_3 : rowKids 5 3=false := by decide +kernel
theorem pair_5_4 : rowKids 5 4=false := by decide +kernel
theorem pair_5_5 : rowKids 5 5=false := by decide +kernel
theorem pair_5_10 : rowKids 5 10=false := by decide +kernel
theorem pair_5_12 : rowKids 5 12=false := by decide +kernel
theorem pair_5_17 : rowKids 5 17=false := by decide +kernel
theorem pair_5_26 : rowKids 5 26=false := by decide +kernel
theorem pair_5_30 : rowKids 5 30=false := by decide +kernel
theorem pair_5_31 : rowKids 5 31=false := by decide +kernel
theorem pair_5_32 : rowKids 5 32=false := by decide +kernel
theorem pair_5_34 : rowKids 5 34=false := by decide +kernel
theorem pair_5_36 : rowKids 5 36=false := by decide +kernel
theorem pair_5_39 : rowKids 5 39=false := by decide +kernel
theorem pair_5_40 : rowKids 5 40=false := by decide +kernel
theorem pair_5_41 : rowKids 5 41=false := by decide +kernel
theorem pair_5_42 : rowKids 5 42=false := by decide +kernel
theorem pair_5_43 : rowKids 5 43=false := by decide +kernel
theorem pair_5_44 : rowKids 5 44=false := by decide +kernel
theorem pair_5_45 : rowKids 5 45=false := by decide +kernel
theorem pair_5_46 : rowKids 5 46=false := by decide +kernel
theorem pair_5_47 : rowKids 5 47=false := by decide +kernel
theorem pair_5_48 : rowKids 5 48=false := by decide +kernel
theorem pair_5_49 : rowKids 5 49=false := by decide +kernel
theorem pair_5_50 : rowKids 5 50=false := by decide +kernel
theorem pair_5_51 : rowKids 5 51=false := by decide +kernel
theorem bound_5 : rowCheck 5=false := row_of_kids 5 (fun b=>Fin.cases pair_5_0 ( Fin.cases pair_5_1 ( Fin.cases pair_5_2 ( Fin.cases pair_5_3 ( Fin.cases pair_5_4 ( Fin.cases pair_5_5 ( Fin.cases pair_5_6 ( Fin.cases pair_5_7 ( Fin.cases pair_5_8 ( Fin.cases pair_5_9 ( Fin.cases pair_5_10 ( Fin.cases pair_5_11 ( Fin.cases pair_5_12 ( Fin.cases pair_5_13 ( Fin.cases pair_5_14 ( Fin.cases pair_5_15 ( Fin.cases pair_5_16 ( Fin.cases pair_5_17 ( Fin.cases pair_5_18 ( Fin.cases pair_5_19 ( Fin.cases pair_5_20 ( Fin.cases pair_5_21 ( Fin.cases pair_5_22 ( Fin.cases pair_5_23 ( Fin.cases pair_5_24 ( Fin.cases pair_5_25 ( Fin.cases pair_5_26 ( Fin.cases pair_5_27 ( Fin.cases pair_5_28 ( Fin.cases pair_5_29 ( Fin.cases pair_5_30 ( Fin.cases pair_5_31 ( Fin.cases pair_5_32 ( Fin.cases pair_5_33 ( Fin.cases pair_5_34 ( Fin.cases pair_5_35 ( Fin.cases pair_5_36 ( Fin.cases pair_5_37 ( Fin.cases pair_5_38 ( Fin.cases pair_5_39 ( Fin.cases pair_5_40 ( Fin.cases pair_5_41 ( Fin.cases pair_5_42 ( Fin.cases pair_5_43 ( Fin.cases pair_5_44 ( Fin.cases pair_5_45 ( Fin.cases pair_5_46 ( Fin.cases pair_5_47 ( Fin.cases pair_5_48 ( Fin.cases pair_5_49 ( Fin.cases pair_5_50 (Fin.cases pair_5_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_5 : tfCheck 5=true := by decide +kernel
end Erdos151Ramsey.Seed53
