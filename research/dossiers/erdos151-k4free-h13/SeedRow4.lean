import BranchCore
import SeedTrio4_5
import SeedTrio4_6
import SeedTrio4_7
import SeedPair4_0
import SeedPair4_1
import SeedPair4_2

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_4_0 : rowKids 4 0=false := by decide +kernel
theorem pair_4_1 : rowKids 4 1=false := by decide +kernel
theorem pair_4_2 : rowKids 4 2=false := by decide +kernel
theorem pair_4_3 : rowKids 4 3=false := by decide +kernel
theorem pair_4_4 : rowKids 4 4=false := by decide +kernel
theorem pair_4_11 : rowKids 4 11=false := by decide +kernel
theorem pair_4_25 : rowKids 4 25=false := by decide +kernel
theorem pair_4_27 : rowKids 4 27=false := by decide +kernel
theorem pair_4_29 : rowKids 4 29=false := by decide +kernel
theorem pair_4_30 : rowKids 4 30=false := by decide +kernel
theorem pair_4_31 : rowKids 4 31=false := by decide +kernel
theorem pair_4_33 : rowKids 4 33=false := by decide +kernel
theorem pair_4_35 : rowKids 4 35=false := by decide +kernel
theorem pair_4_38 : rowKids 4 38=false := by decide +kernel
theorem pair_4_39 : rowKids 4 39=false := by decide +kernel
theorem pair_4_40 : rowKids 4 40=false := by decide +kernel
theorem pair_4_41 : rowKids 4 41=false := by decide +kernel
theorem pair_4_42 : rowKids 4 42=false := by decide +kernel
theorem pair_4_43 : rowKids 4 43=false := by decide +kernel
theorem pair_4_44 : rowKids 4 44=false := by decide +kernel
theorem pair_4_45 : rowKids 4 45=false := by decide +kernel
theorem pair_4_46 : rowKids 4 46=false := by decide +kernel
theorem pair_4_47 : rowKids 4 47=false := by decide +kernel
theorem pair_4_48 : rowKids 4 48=false := by decide +kernel
theorem pair_4_49 : rowKids 4 49=false := by decide +kernel
theorem pair_4_50 : rowKids 4 50=false := by decide +kernel
theorem pair_4_51 : rowKids 4 51=false := by decide +kernel
theorem bound_4 : rowCheck 4=false := row_of_kids 4 (fun b=>Fin.cases pair_4_0 ( Fin.cases pair_4_1 ( Fin.cases pair_4_2 ( Fin.cases pair_4_3 ( Fin.cases pair_4_4 ( Fin.cases pair_4_5 ( Fin.cases pair_4_6 ( Fin.cases pair_4_7 ( Fin.cases pair_4_8 ( Fin.cases pair_4_9 ( Fin.cases pair_4_10 ( Fin.cases pair_4_11 ( Fin.cases pair_4_12 ( Fin.cases pair_4_13 ( Fin.cases pair_4_14 ( Fin.cases pair_4_15 ( Fin.cases pair_4_16 ( Fin.cases pair_4_17 ( Fin.cases pair_4_18 ( Fin.cases pair_4_19 ( Fin.cases pair_4_20 ( Fin.cases pair_4_21 ( Fin.cases pair_4_22 ( Fin.cases pair_4_23 ( Fin.cases pair_4_24 ( Fin.cases pair_4_25 ( Fin.cases pair_4_26 ( Fin.cases pair_4_27 ( Fin.cases pair_4_28 ( Fin.cases pair_4_29 ( Fin.cases pair_4_30 ( Fin.cases pair_4_31 ( Fin.cases pair_4_32 ( Fin.cases pair_4_33 ( Fin.cases pair_4_34 ( Fin.cases pair_4_35 ( Fin.cases pair_4_36 ( Fin.cases pair_4_37 ( Fin.cases pair_4_38 ( Fin.cases pair_4_39 ( Fin.cases pair_4_40 ( Fin.cases pair_4_41 ( Fin.cases pair_4_42 ( Fin.cases pair_4_43 ( Fin.cases pair_4_44 ( Fin.cases pair_4_45 ( Fin.cases pair_4_46 ( Fin.cases pair_4_47 ( Fin.cases pair_4_48 ( Fin.cases pair_4_49 ( Fin.cases pair_4_50 (Fin.cases pair_4_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_4 : tfCheck 4=true := by decide +kernel
end Erdos151Ramsey.Seed53
