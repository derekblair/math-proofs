import BranchCore
import SeedPair11_0
import SeedPair11_1

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096
theorem pair_11_0 : rowKids 11 0=false := by decide +kernel
theorem pair_11_1 : rowKids 11 1=false := by decide +kernel
theorem pair_11_2 : rowKids 11 2=false := by decide +kernel
theorem pair_11_3 : rowKids 11 3=false := by decide +kernel
theorem pair_11_4 : rowKids 11 4=false := by decide +kernel
theorem pair_11_5 : rowKids 11 5=false := by decide +kernel
theorem pair_11_6 : rowKids 11 6=false := by decide +kernel
theorem pair_11_7 : rowKids 11 7=false := by decide +kernel
theorem pair_11_8 : rowKids 11 8=false := by decide +kernel
theorem pair_11_9 : rowKids 11 9=false := by decide +kernel
theorem pair_11_10 : rowKids 11 10=false := by decide +kernel
theorem pair_11_11 : rowKids 11 11=false := by decide +kernel
theorem pair_11_18 : rowKids 11 18=false := by decide +kernel
theorem pair_11_23 : rowKids 11 23=false := by decide +kernel
theorem pair_11_33 : rowKids 11 33=false := by decide +kernel
theorem pair_11_34 : rowKids 11 34=false := by decide +kernel
theorem pair_11_35 : rowKids 11 35=false := by decide +kernel
theorem pair_11_36 : rowKids 11 36=false := by decide +kernel
theorem pair_11_37 : rowKids 11 37=false := by decide +kernel
theorem pair_11_38 : rowKids 11 38=false := by decide +kernel
theorem pair_11_39 : rowKids 11 39=false := by decide +kernel
theorem pair_11_40 : rowKids 11 40=false := by decide +kernel
theorem pair_11_41 : rowKids 11 41=false := by decide +kernel
theorem pair_11_42 : rowKids 11 42=false := by decide +kernel
theorem pair_11_43 : rowKids 11 43=false := by decide +kernel
theorem pair_11_44 : rowKids 11 44=false := by decide +kernel
theorem pair_11_45 : rowKids 11 45=false := by decide +kernel
theorem pair_11_46 : rowKids 11 46=false := by decide +kernel
theorem pair_11_47 : rowKids 11 47=false := by decide +kernel
theorem pair_11_48 : rowKids 11 48=false := by decide +kernel
theorem pair_11_49 : rowKids 11 49=false := by decide +kernel
theorem pair_11_50 : rowKids 11 50=false := by decide +kernel
theorem pair_11_51 : rowKids 11 51=false := by decide +kernel
theorem bound_11 : rowCheck 11=false := row_of_kids 11 (fun b=>Fin.cases pair_11_0 ( Fin.cases pair_11_1 ( Fin.cases pair_11_2 ( Fin.cases pair_11_3 ( Fin.cases pair_11_4 ( Fin.cases pair_11_5 ( Fin.cases pair_11_6 ( Fin.cases pair_11_7 ( Fin.cases pair_11_8 ( Fin.cases pair_11_9 ( Fin.cases pair_11_10 ( Fin.cases pair_11_11 ( Fin.cases pair_11_12 ( Fin.cases pair_11_13 ( Fin.cases pair_11_14 ( Fin.cases pair_11_15 ( Fin.cases pair_11_16 ( Fin.cases pair_11_17 ( Fin.cases pair_11_18 ( Fin.cases pair_11_19 ( Fin.cases pair_11_20 ( Fin.cases pair_11_21 ( Fin.cases pair_11_22 ( Fin.cases pair_11_23 ( Fin.cases pair_11_24 ( Fin.cases pair_11_25 ( Fin.cases pair_11_26 ( Fin.cases pair_11_27 ( Fin.cases pair_11_28 ( Fin.cases pair_11_29 ( Fin.cases pair_11_30 ( Fin.cases pair_11_31 ( Fin.cases pair_11_32 ( Fin.cases pair_11_33 ( Fin.cases pair_11_34 ( Fin.cases pair_11_35 ( Fin.cases pair_11_36 ( Fin.cases pair_11_37 ( Fin.cases pair_11_38 ( Fin.cases pair_11_39 ( Fin.cases pair_11_40 ( Fin.cases pair_11_41 ( Fin.cases pair_11_42 ( Fin.cases pair_11_43 ( Fin.cases pair_11_44 ( Fin.cases pair_11_45 ( Fin.cases pair_11_46 ( Fin.cases pair_11_47 ( Fin.cases pair_11_48 ( Fin.cases pair_11_49 ( Fin.cases pair_11_50 (Fin.cases pair_11_51 (fun t : Fin 0=>t.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))) b)
theorem tri_11 : tfCheck 11=true := by decide +kernel
end Erdos151Ramsey.Seed53
