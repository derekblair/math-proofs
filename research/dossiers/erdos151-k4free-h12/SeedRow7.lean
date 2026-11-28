import BranchCore
import SeedTrio7_8
import SeedTrio7_9
import SeedTrio7_10
import SeedPair7_0

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_7_0 : rowKids 7 0=false := by decide +kernel
theorem pair_7_1 : rowKids 7 1=false := by decide +kernel
theorem pair_7_2 : rowKids 7 2=false := by decide +kernel
theorem pair_7_3 : rowKids 7 3=false := by decide +kernel
theorem pair_7_4 : rowKids 7 4=false := by decide +kernel
theorem pair_7_5 : rowKids 7 5=false := by decide +kernel
theorem pair_7_6 : rowKids 7 6=false := by decide +kernel
theorem pair_7_7 : rowKids 7 7=false := by decide +kernel
theorem pair_7_22 : rowKids 7 22=false := by decide +kernel
theorem pair_7_28 : rowKids 7 28=false := by decide +kernel
theorem pair_7_30 : rowKids 7 30=false := by decide +kernel
theorem pair_7_32 : rowKids 7 32=false := by decide +kernel
theorem pair_7_33 : rowKids 7 33=false := by decide +kernel
theorem pair_7_34 : rowKids 7 34=false := by decide +kernel
theorem pair_7_36 : rowKids 7 36=false := by decide +kernel
theorem pair_7_37 : rowKids 7 37=false := by decide +kernel
theorem pair_7_38 : rowKids 7 38=false := by decide +kernel
theorem pair_7_39 : rowKids 7 39=false := by decide +kernel
theorem pair_7_40 : rowKids 7 40=false := by decide +kernel
theorem pair_7_41 : rowKids 7 41=false := by decide +kernel
theorem pair_7_42 : rowKids 7 42=false := by decide +kernel
theorem pair_7_43 : rowKids 7 43=false := by decide +kernel
theorem pair_7_44 : rowKids 7 44=false := by decide +kernel
theorem pair_7_45 : rowKids 7 45=false := by decide +kernel
theorem pair_7_46 : rowKids 7 46=false := by decide +kernel
theorem pair_7_47 : rowKids 7 47=false := by decide +kernel
theorem pair_7_48 : rowKids 7 48=false := by decide +kernel
theorem pair_7_49 : rowKids 7 49=false := by decide +kernel
theorem pair_7_50 : rowKids 7 50=false := by decide +kernel
theorem pair_7_51 : rowKids 7 51=false := by decide +kernel
theorem bound_7 : rowCheck 7=false := row_of_kids 7 (fun b=>Fin.cases pair_7_0 ( Fin.cases pair_7_1 ( Fin.cases pair_7_2 ( Fin.cases pair_7_3 ( Fin.cases pair_7_4 ( Fin.cases pair_7_5 ( Fin.cases pair_7_6 ( Fin.cases pair_7_7 ( Fin.cases pair_7_8 ( Fin.cases pair_7_9 ( Fin.cases pair_7_10 ( Fin.cases pair_7_11 ( Fin.cases pair_7_12 ( Fin.cases pair_7_13 ( Fin.cases pair_7_14 ( Fin.cases pair_7_15 ( Fin.cases pair_7_16 ( Fin.cases pair_7_17 ( Fin.cases pair_7_18 ( Fin.cases pair_7_19 ( Fin.cases pair_7_20 ( Fin.cases pair_7_21 ( Fin.cases pair_7_22 ( Fin.cases pair_7_23 ( Fin.cases pair_7_24 ( Fin.cases pair_7_25 ( Fin.cases pair_7_26 ( Fin.cases pair_7_27 ( Fin.cases pair_7_28 ( Fin.cases pair_7_29 ( Fin.cases pair_7_30 ( Fin.cases pair_7_31 ( Fin.cases pair_7_32 ( Fin.cases pair_7_33 ( Fin.cases pair_7_34 ( Fin.cases pair_7_35 ( Fin.cases pair_7_36 ( Fin.cases pair_7_37 ( Fin.cases pair_7_38 ( Fin.cases pair_7_39 ( Fin.cases pair_7_40 ( Fin.cases pair_7_41 ( Fin.cases pair_7_42 ( Fin.cases pair_7_43 ( Fin.cases pair_7_44 ( Fin.cases pair_7_45 ( Fin.cases pair_7_46 ( Fin.cases pair_7_47 ( Fin.cases pair_7_48 ( Fin.cases pair_7_49 ( Fin.cases pair_7_50 (Fin.cases pair_7_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_7 : tfCheck 7=true := by decide +kernel
end Erdos151Ramsey.Seed53
