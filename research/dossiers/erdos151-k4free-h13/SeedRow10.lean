import BranchCore
import SeedPair10_0
import SeedPair10_1
import SeedPair10_2
import SeedPair10_3

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_10_0 : rowKids 10 0=false := by decide +kernel
theorem pair_10_1 : rowKids 10 1=false := by decide +kernel
theorem pair_10_2 : rowKids 10 2=false := by decide +kernel
theorem pair_10_3 : rowKids 10 3=false := by decide +kernel
theorem pair_10_4 : rowKids 10 4=false := by decide +kernel
theorem pair_10_5 : rowKids 10 5=false := by decide +kernel
theorem pair_10_6 : rowKids 10 6=false := by decide +kernel
theorem pair_10_7 : rowKids 10 7=false := by decide +kernel
theorem pair_10_8 : rowKids 10 8=false := by decide +kernel
theorem pair_10_9 : rowKids 10 9=false := by decide +kernel
theorem pair_10_10 : rowKids 10 10=false := by decide +kernel
theorem pair_10_22 : rowKids 10 22=false := by decide +kernel
theorem pair_10_33 : rowKids 10 33=false := by decide +kernel
theorem pair_10_36 : rowKids 10 36=false := by decide +kernel
theorem pair_10_37 : rowKids 10 37=false := by decide +kernel
theorem pair_10_38 : rowKids 10 38=false := by decide +kernel
theorem pair_10_39 : rowKids 10 39=false := by decide +kernel
theorem pair_10_40 : rowKids 10 40=false := by decide +kernel
theorem pair_10_41 : rowKids 10 41=false := by decide +kernel
theorem pair_10_42 : rowKids 10 42=false := by decide +kernel
theorem pair_10_43 : rowKids 10 43=false := by decide +kernel
theorem pair_10_44 : rowKids 10 44=false := by decide +kernel
theorem pair_10_45 : rowKids 10 45=false := by decide +kernel
theorem pair_10_46 : rowKids 10 46=false := by decide +kernel
theorem pair_10_47 : rowKids 10 47=false := by decide +kernel
theorem pair_10_48 : rowKids 10 48=false := by decide +kernel
theorem pair_10_49 : rowKids 10 49=false := by decide +kernel
theorem pair_10_50 : rowKids 10 50=false := by decide +kernel
theorem pair_10_51 : rowKids 10 51=false := by decide +kernel
theorem bound_10 : rowCheck 10=false := row_of_kids 10 (fun b=>Fin.cases pair_10_0 ( Fin.cases pair_10_1 ( Fin.cases pair_10_2 ( Fin.cases pair_10_3 ( Fin.cases pair_10_4 ( Fin.cases pair_10_5 ( Fin.cases pair_10_6 ( Fin.cases pair_10_7 ( Fin.cases pair_10_8 ( Fin.cases pair_10_9 ( Fin.cases pair_10_10 ( Fin.cases pair_10_11 ( Fin.cases pair_10_12 ( Fin.cases pair_10_13 ( Fin.cases pair_10_14 ( Fin.cases pair_10_15 ( Fin.cases pair_10_16 ( Fin.cases pair_10_17 ( Fin.cases pair_10_18 ( Fin.cases pair_10_19 ( Fin.cases pair_10_20 ( Fin.cases pair_10_21 ( Fin.cases pair_10_22 ( Fin.cases pair_10_23 ( Fin.cases pair_10_24 ( Fin.cases pair_10_25 ( Fin.cases pair_10_26 ( Fin.cases pair_10_27 ( Fin.cases pair_10_28 ( Fin.cases pair_10_29 ( Fin.cases pair_10_30 ( Fin.cases pair_10_31 ( Fin.cases pair_10_32 ( Fin.cases pair_10_33 ( Fin.cases pair_10_34 ( Fin.cases pair_10_35 ( Fin.cases pair_10_36 ( Fin.cases pair_10_37 ( Fin.cases pair_10_38 ( Fin.cases pair_10_39 ( Fin.cases pair_10_40 ( Fin.cases pair_10_41 ( Fin.cases pair_10_42 ( Fin.cases pair_10_43 ( Fin.cases pair_10_44 ( Fin.cases pair_10_45 ( Fin.cases pair_10_46 ( Fin.cases pair_10_47 ( Fin.cases pair_10_48 ( Fin.cases pair_10_49 ( Fin.cases pair_10_50 (Fin.cases pair_10_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_10 : tfCheck 10=true := by decide +kernel
end Erdos151Ramsey.Seed53
