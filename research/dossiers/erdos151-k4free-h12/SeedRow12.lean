import BranchCore
import SeedPair12_0
import SeedPair12_1

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_12_0 : rowKids 12 0=false := by decide +kernel
theorem pair_12_1 : rowKids 12 1=false := by decide +kernel
theorem pair_12_2 : rowKids 12 2=false := by decide +kernel
theorem pair_12_3 : rowKids 12 3=false := by decide +kernel
theorem pair_12_4 : rowKids 12 4=false := by decide +kernel
theorem pair_12_5 : rowKids 12 5=false := by decide +kernel
theorem pair_12_6 : rowKids 12 6=false := by decide +kernel
theorem pair_12_7 : rowKids 12 7=false := by decide +kernel
theorem pair_12_8 : rowKids 12 8=false := by decide +kernel
theorem pair_12_9 : rowKids 12 9=false := by decide +kernel
theorem pair_12_10 : rowKids 12 10=false := by decide +kernel
theorem pair_12_11 : rowKids 12 11=false := by decide +kernel
theorem pair_12_12 : rowKids 12 12=false := by decide +kernel
theorem pair_12_19 : rowKids 12 19=false := by decide +kernel
theorem pair_12_21 : rowKids 12 21=false := by decide +kernel
theorem pair_12_33 : rowKids 12 33=false := by decide +kernel
theorem pair_12_34 : rowKids 12 34=false := by decide +kernel
theorem pair_12_35 : rowKids 12 35=false := by decide +kernel
theorem pair_12_36 : rowKids 12 36=false := by decide +kernel
theorem pair_12_37 : rowKids 12 37=false := by decide +kernel
theorem pair_12_38 : rowKids 12 38=false := by decide +kernel
theorem pair_12_39 : rowKids 12 39=false := by decide +kernel
theorem pair_12_40 : rowKids 12 40=false := by decide +kernel
theorem pair_12_41 : rowKids 12 41=false := by decide +kernel
theorem pair_12_42 : rowKids 12 42=false := by decide +kernel
theorem pair_12_43 : rowKids 12 43=false := by decide +kernel
theorem pair_12_44 : rowKids 12 44=false := by decide +kernel
theorem pair_12_45 : rowKids 12 45=false := by decide +kernel
theorem pair_12_46 : rowKids 12 46=false := by decide +kernel
theorem pair_12_47 : rowKids 12 47=false := by decide +kernel
theorem pair_12_48 : rowKids 12 48=false := by decide +kernel
theorem pair_12_49 : rowKids 12 49=false := by decide +kernel
theorem pair_12_50 : rowKids 12 50=false := by decide +kernel
theorem pair_12_51 : rowKids 12 51=false := by decide +kernel
theorem bound_12 : rowCheck 12=false := row_of_kids 12 (fun b=>Fin.cases pair_12_0 ( Fin.cases pair_12_1 ( Fin.cases pair_12_2 ( Fin.cases pair_12_3 ( Fin.cases pair_12_4 ( Fin.cases pair_12_5 ( Fin.cases pair_12_6 ( Fin.cases pair_12_7 ( Fin.cases pair_12_8 ( Fin.cases pair_12_9 ( Fin.cases pair_12_10 ( Fin.cases pair_12_11 ( Fin.cases pair_12_12 ( Fin.cases pair_12_13 ( Fin.cases pair_12_14 ( Fin.cases pair_12_15 ( Fin.cases pair_12_16 ( Fin.cases pair_12_17 ( Fin.cases pair_12_18 ( Fin.cases pair_12_19 ( Fin.cases pair_12_20 ( Fin.cases pair_12_21 ( Fin.cases pair_12_22 ( Fin.cases pair_12_23 ( Fin.cases pair_12_24 ( Fin.cases pair_12_25 ( Fin.cases pair_12_26 ( Fin.cases pair_12_27 ( Fin.cases pair_12_28 ( Fin.cases pair_12_29 ( Fin.cases pair_12_30 ( Fin.cases pair_12_31 ( Fin.cases pair_12_32 ( Fin.cases pair_12_33 ( Fin.cases pair_12_34 ( Fin.cases pair_12_35 ( Fin.cases pair_12_36 ( Fin.cases pair_12_37 ( Fin.cases pair_12_38 ( Fin.cases pair_12_39 ( Fin.cases pair_12_40 ( Fin.cases pair_12_41 ( Fin.cases pair_12_42 ( Fin.cases pair_12_43 ( Fin.cases pair_12_44 ( Fin.cases pair_12_45 ( Fin.cases pair_12_46 ( Fin.cases pair_12_47 ( Fin.cases pair_12_48 ( Fin.cases pair_12_49 ( Fin.cases pair_12_50 (Fin.cases pair_12_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_12 : tfCheck 12=true := by decide +kernel
end Erdos151Ramsey.Seed53
