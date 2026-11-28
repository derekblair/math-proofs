import BranchCore
import SeedTrio6_7
import SeedTrio6_8
import SeedPair6_0
import SeedPair6_1
import SeedPair6_2

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_6_0 : rowKids 6 0=false := by decide +kernel
theorem pair_6_1 : rowKids 6 1=false := by decide +kernel
theorem pair_6_2 : rowKids 6 2=false := by decide +kernel
theorem pair_6_3 : rowKids 6 3=false := by decide +kernel
theorem pair_6_4 : rowKids 6 4=false := by decide +kernel
theorem pair_6_5 : rowKids 6 5=false := by decide +kernel
theorem pair_6_6 : rowKids 6 6=false := by decide +kernel
theorem pair_6_13 : rowKids 6 13=false := by decide +kernel
theorem pair_6_18 : rowKids 6 18=false := by decide +kernel
theorem pair_6_27 : rowKids 6 27=false := by decide +kernel
theorem pair_6_29 : rowKids 6 29=false := by decide +kernel
theorem pair_6_31 : rowKids 6 31=false := by decide +kernel
theorem pair_6_32 : rowKids 6 32=false := by decide +kernel
theorem pair_6_33 : rowKids 6 33=false := by decide +kernel
theorem pair_6_35 : rowKids 6 35=false := by decide +kernel
theorem pair_6_37 : rowKids 6 37=false := by decide +kernel
theorem pair_6_38 : rowKids 6 38=false := by decide +kernel
theorem pair_6_40 : rowKids 6 40=false := by decide +kernel
theorem pair_6_41 : rowKids 6 41=false := by decide +kernel
theorem pair_6_42 : rowKids 6 42=false := by decide +kernel
theorem pair_6_43 : rowKids 6 43=false := by decide +kernel
theorem pair_6_44 : rowKids 6 44=false := by decide +kernel
theorem pair_6_45 : rowKids 6 45=false := by decide +kernel
theorem pair_6_46 : rowKids 6 46=false := by decide +kernel
theorem pair_6_47 : rowKids 6 47=false := by decide +kernel
theorem pair_6_48 : rowKids 6 48=false := by decide +kernel
theorem pair_6_49 : rowKids 6 49=false := by decide +kernel
theorem pair_6_50 : rowKids 6 50=false := by decide +kernel
theorem pair_6_51 : rowKids 6 51=false := by decide +kernel
theorem bound_6 : rowCheck 6=false := row_of_kids 6 (fun b=>Fin.cases pair_6_0 ( Fin.cases pair_6_1 ( Fin.cases pair_6_2 ( Fin.cases pair_6_3 ( Fin.cases pair_6_4 ( Fin.cases pair_6_5 ( Fin.cases pair_6_6 ( Fin.cases pair_6_7 ( Fin.cases pair_6_8 ( Fin.cases pair_6_9 ( Fin.cases pair_6_10 ( Fin.cases pair_6_11 ( Fin.cases pair_6_12 ( Fin.cases pair_6_13 ( Fin.cases pair_6_14 ( Fin.cases pair_6_15 ( Fin.cases pair_6_16 ( Fin.cases pair_6_17 ( Fin.cases pair_6_18 ( Fin.cases pair_6_19 ( Fin.cases pair_6_20 ( Fin.cases pair_6_21 ( Fin.cases pair_6_22 ( Fin.cases pair_6_23 ( Fin.cases pair_6_24 ( Fin.cases pair_6_25 ( Fin.cases pair_6_26 ( Fin.cases pair_6_27 ( Fin.cases pair_6_28 ( Fin.cases pair_6_29 ( Fin.cases pair_6_30 ( Fin.cases pair_6_31 ( Fin.cases pair_6_32 ( Fin.cases pair_6_33 ( Fin.cases pair_6_34 ( Fin.cases pair_6_35 ( Fin.cases pair_6_36 ( Fin.cases pair_6_37 ( Fin.cases pair_6_38 ( Fin.cases pair_6_39 ( Fin.cases pair_6_40 ( Fin.cases pair_6_41 ( Fin.cases pair_6_42 ( Fin.cases pair_6_43 ( Fin.cases pair_6_44 ( Fin.cases pair_6_45 ( Fin.cases pair_6_46 ( Fin.cases pair_6_47 ( Fin.cases pair_6_48 ( Fin.cases pair_6_49 ( Fin.cases pair_6_50 (Fin.cases pair_6_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_6 : tfCheck 6=true := by decide +kernel
end Erdos151Ramsey.Seed53
