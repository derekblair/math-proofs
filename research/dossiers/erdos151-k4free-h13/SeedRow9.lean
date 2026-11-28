import BranchCore
import SeedPair9_0
import SeedPair9_1
import SeedPair9_2

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_9_0 : rowKids 9 0=false := by decide +kernel
theorem pair_9_1 : rowKids 9 1=false := by decide +kernel
theorem pair_9_2 : rowKids 9 2=false := by decide +kernel
theorem pair_9_3 : rowKids 9 3=false := by decide +kernel
theorem pair_9_4 : rowKids 9 4=false := by decide +kernel
theorem pair_9_5 : rowKids 9 5=false := by decide +kernel
theorem pair_9_6 : rowKids 9 6=false := by decide +kernel
theorem pair_9_7 : rowKids 9 7=false := by decide +kernel
theorem pair_9_8 : rowKids 9 8=false := by decide +kernel
theorem pair_9_9 : rowKids 9 9=false := by decide +kernel
theorem pair_9_10 : rowKids 9 10=false := by decide +kernel
theorem pair_9_16 : rowKids 9 16=false := by decide +kernel
theorem pair_9_19 : rowKids 9 19=false := by decide +kernel
theorem pair_9_21 : rowKids 9 21=false := by decide +kernel
theorem pair_9_30 : rowKids 9 30=false := by decide +kernel
theorem pair_9_32 : rowKids 9 32=false := by decide +kernel
theorem pair_9_34 : rowKids 9 34=false := by decide +kernel
theorem pair_9_35 : rowKids 9 35=false := by decide +kernel
theorem pair_9_36 : rowKids 9 36=false := by decide +kernel
theorem pair_9_38 : rowKids 9 38=false := by decide +kernel
theorem pair_9_42 : rowKids 9 42=false := by decide +kernel
theorem pair_9_43 : rowKids 9 43=false := by decide +kernel
theorem pair_9_44 : rowKids 9 44=false := by decide +kernel
theorem pair_9_45 : rowKids 9 45=false := by decide +kernel
theorem pair_9_46 : rowKids 9 46=false := by decide +kernel
theorem pair_9_47 : rowKids 9 47=false := by decide +kernel
theorem pair_9_48 : rowKids 9 48=false := by decide +kernel
theorem pair_9_49 : rowKids 9 49=false := by decide +kernel
theorem pair_9_50 : rowKids 9 50=false := by decide +kernel
theorem pair_9_51 : rowKids 9 51=false := by decide +kernel
theorem bound_9 : rowCheck 9=false := row_of_kids 9 (fun b=>Fin.cases pair_9_0 ( Fin.cases pair_9_1 ( Fin.cases pair_9_2 ( Fin.cases pair_9_3 ( Fin.cases pair_9_4 ( Fin.cases pair_9_5 ( Fin.cases pair_9_6 ( Fin.cases pair_9_7 ( Fin.cases pair_9_8 ( Fin.cases pair_9_9 ( Fin.cases pair_9_10 ( Fin.cases pair_9_11 ( Fin.cases pair_9_12 ( Fin.cases pair_9_13 ( Fin.cases pair_9_14 ( Fin.cases pair_9_15 ( Fin.cases pair_9_16 ( Fin.cases pair_9_17 ( Fin.cases pair_9_18 ( Fin.cases pair_9_19 ( Fin.cases pair_9_20 ( Fin.cases pair_9_21 ( Fin.cases pair_9_22 ( Fin.cases pair_9_23 ( Fin.cases pair_9_24 ( Fin.cases pair_9_25 ( Fin.cases pair_9_26 ( Fin.cases pair_9_27 ( Fin.cases pair_9_28 ( Fin.cases pair_9_29 ( Fin.cases pair_9_30 ( Fin.cases pair_9_31 ( Fin.cases pair_9_32 ( Fin.cases pair_9_33 ( Fin.cases pair_9_34 ( Fin.cases pair_9_35 ( Fin.cases pair_9_36 ( Fin.cases pair_9_37 ( Fin.cases pair_9_38 ( Fin.cases pair_9_39 ( Fin.cases pair_9_40 ( Fin.cases pair_9_41 ( Fin.cases pair_9_42 ( Fin.cases pair_9_43 ( Fin.cases pair_9_44 ( Fin.cases pair_9_45 ( Fin.cases pair_9_46 ( Fin.cases pair_9_47 ( Fin.cases pair_9_48 ( Fin.cases pair_9_49 ( Fin.cases pair_9_50 (Fin.cases pair_9_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_9 : tfCheck 9=true := by decide +kernel
end Erdos151Ramsey.Seed53
