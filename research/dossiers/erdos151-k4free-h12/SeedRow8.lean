import BranchCore
import SeedPair8_0
import SeedPair8_1
import SeedPair8_2
import SeedPair8_3

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_8_0 : rowKids 8 0=false := by decide +kernel
theorem pair_8_1 : rowKids 8 1=false := by decide +kernel
theorem pair_8_2 : rowKids 8 2=false := by decide +kernel
theorem pair_8_3 : rowKids 8 3=false := by decide +kernel
theorem pair_8_4 : rowKids 8 4=false := by decide +kernel
theorem pair_8_5 : rowKids 8 5=false := by decide +kernel
theorem pair_8_6 : rowKids 8 6=false := by decide +kernel
theorem pair_8_7 : rowKids 8 7=false := by decide +kernel
theorem pair_8_8 : rowKids 8 8=false := by decide +kernel
theorem pair_8_15 : rowKids 8 15=false := by decide +kernel
theorem pair_8_18 : rowKids 8 18=false := by decide +kernel
theorem pair_8_20 : rowKids 8 20=false := by decide +kernel
theorem pair_8_29 : rowKids 8 29=false := by decide +kernel
theorem pair_8_31 : rowKids 8 31=false := by decide +kernel
theorem pair_8_33 : rowKids 8 33=false := by decide +kernel
theorem pair_8_34 : rowKids 8 34=false := by decide +kernel
theorem pair_8_35 : rowKids 8 35=false := by decide +kernel
theorem pair_8_39 : rowKids 8 39=false := by decide +kernel
theorem pair_8_42 : rowKids 8 42=false := by decide +kernel
theorem pair_8_43 : rowKids 8 43=false := by decide +kernel
theorem pair_8_44 : rowKids 8 44=false := by decide +kernel
theorem pair_8_45 : rowKids 8 45=false := by decide +kernel
theorem pair_8_46 : rowKids 8 46=false := by decide +kernel
theorem pair_8_47 : rowKids 8 47=false := by decide +kernel
theorem pair_8_48 : rowKids 8 48=false := by decide +kernel
theorem pair_8_49 : rowKids 8 49=false := by decide +kernel
theorem pair_8_50 : rowKids 8 50=false := by decide +kernel
theorem pair_8_51 : rowKids 8 51=false := by decide +kernel
theorem bound_8 : rowCheck 8=false := row_of_kids 8 (fun b=>Fin.cases pair_8_0 ( Fin.cases pair_8_1 ( Fin.cases pair_8_2 ( Fin.cases pair_8_3 ( Fin.cases pair_8_4 ( Fin.cases pair_8_5 ( Fin.cases pair_8_6 ( Fin.cases pair_8_7 ( Fin.cases pair_8_8 ( Fin.cases pair_8_9 ( Fin.cases pair_8_10 ( Fin.cases pair_8_11 ( Fin.cases pair_8_12 ( Fin.cases pair_8_13 ( Fin.cases pair_8_14 ( Fin.cases pair_8_15 ( Fin.cases pair_8_16 ( Fin.cases pair_8_17 ( Fin.cases pair_8_18 ( Fin.cases pair_8_19 ( Fin.cases pair_8_20 ( Fin.cases pair_8_21 ( Fin.cases pair_8_22 ( Fin.cases pair_8_23 ( Fin.cases pair_8_24 ( Fin.cases pair_8_25 ( Fin.cases pair_8_26 ( Fin.cases pair_8_27 ( Fin.cases pair_8_28 ( Fin.cases pair_8_29 ( Fin.cases pair_8_30 ( Fin.cases pair_8_31 ( Fin.cases pair_8_32 ( Fin.cases pair_8_33 ( Fin.cases pair_8_34 ( Fin.cases pair_8_35 ( Fin.cases pair_8_36 ( Fin.cases pair_8_37 ( Fin.cases pair_8_38 ( Fin.cases pair_8_39 ( Fin.cases pair_8_40 ( Fin.cases pair_8_41 ( Fin.cases pair_8_42 ( Fin.cases pair_8_43 ( Fin.cases pair_8_44 ( Fin.cases pair_8_45 ( Fin.cases pair_8_46 ( Fin.cases pair_8_47 ( Fin.cases pair_8_48 ( Fin.cases pair_8_49 ( Fin.cases pair_8_50 (Fin.cases pair_8_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_8 : tfCheck 8=true := by decide +kernel
end Erdos151Ramsey.Seed53
