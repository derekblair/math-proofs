import BranchCore
import SeedTrio3_5
import SeedTrio3_7
import SeedPair3_0
import SeedPair3_1
import SeedPair3_2
import SeedPair3_3
import SeedPair3_4

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_3_0 : rowKids 3 0=false := by decide +kernel
theorem pair_3_1 : rowKids 3 1=false := by decide +kernel
theorem pair_3_2 : rowKids 3 2=false := by decide +kernel
theorem pair_3_3 : rowKids 3 3=false := by decide +kernel
theorem pair_3_10 : rowKids 3 10=false := by decide +kernel
theorem pair_3_14 : rowKids 3 14=false := by decide +kernel
theorem pair_3_15 : rowKids 3 15=false := by decide +kernel
theorem pair_3_19 : rowKids 3 19=false := by decide +kernel
theorem pair_3_24 : rowKids 3 24=false := by decide +kernel
theorem pair_3_28 : rowKids 3 28=false := by decide +kernel
theorem pair_3_30 : rowKids 3 30=false := by decide +kernel
theorem pair_3_32 : rowKids 3 32=false := by decide +kernel
theorem pair_3_34 : rowKids 3 34=false := by decide +kernel
theorem pair_3_38 : rowKids 3 38=false := by decide +kernel
theorem pair_3_39 : rowKids 3 39=false := by decide +kernel
theorem pair_3_40 : rowKids 3 40=false := by decide +kernel
theorem pair_3_41 : rowKids 3 41=false := by decide +kernel
theorem pair_3_42 : rowKids 3 42=false := by decide +kernel
theorem pair_3_43 : rowKids 3 43=false := by decide +kernel
theorem pair_3_44 : rowKids 3 44=false := by decide +kernel
theorem pair_3_45 : rowKids 3 45=false := by decide +kernel
theorem pair_3_46 : rowKids 3 46=false := by decide +kernel
theorem pair_3_47 : rowKids 3 47=false := by decide +kernel
theorem pair_3_48 : rowKids 3 48=false := by decide +kernel
theorem pair_3_49 : rowKids 3 49=false := by decide +kernel
theorem pair_3_50 : rowKids 3 50=false := by decide +kernel
theorem pair_3_51 : rowKids 3 51=false := by decide +kernel
theorem bound_3 : rowCheck 3=false := row_of_kids 3 (fun b=>Fin.cases pair_3_0 ( Fin.cases pair_3_1 ( Fin.cases pair_3_2 ( Fin.cases pair_3_3 ( Fin.cases pair_3_4 ( Fin.cases pair_3_5 ( Fin.cases pair_3_6 ( Fin.cases pair_3_7 ( Fin.cases pair_3_8 ( Fin.cases pair_3_9 ( Fin.cases pair_3_10 ( Fin.cases pair_3_11 ( Fin.cases pair_3_12 ( Fin.cases pair_3_13 ( Fin.cases pair_3_14 ( Fin.cases pair_3_15 ( Fin.cases pair_3_16 ( Fin.cases pair_3_17 ( Fin.cases pair_3_18 ( Fin.cases pair_3_19 ( Fin.cases pair_3_20 ( Fin.cases pair_3_21 ( Fin.cases pair_3_22 ( Fin.cases pair_3_23 ( Fin.cases pair_3_24 ( Fin.cases pair_3_25 ( Fin.cases pair_3_26 ( Fin.cases pair_3_27 ( Fin.cases pair_3_28 ( Fin.cases pair_3_29 ( Fin.cases pair_3_30 ( Fin.cases pair_3_31 ( Fin.cases pair_3_32 ( Fin.cases pair_3_33 ( Fin.cases pair_3_34 ( Fin.cases pair_3_35 ( Fin.cases pair_3_36 ( Fin.cases pair_3_37 ( Fin.cases pair_3_38 ( Fin.cases pair_3_39 ( Fin.cases pair_3_40 ( Fin.cases pair_3_41 ( Fin.cases pair_3_42 ( Fin.cases pair_3_43 ( Fin.cases pair_3_44 ( Fin.cases pair_3_45 ( Fin.cases pair_3_46 ( Fin.cases pair_3_47 ( Fin.cases pair_3_48 ( Fin.cases pair_3_49 ( Fin.cases pair_3_50 (Fin.cases pair_3_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_3 : tfCheck 3=true := by decide +kernel
end Erdos151Ramsey.Seed53
