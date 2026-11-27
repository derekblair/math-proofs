import HaarC5C000
import HaarC5C024
import HaarC5C048
import HaarC5C072
import HaarC5C096
import HaarC5C120
import HaarC5C144
import HaarC5C168
import HaarC5C192
import HaarC5C216
import HaarC5C240
import HaarC5C264
import HaarC5C288
import HaarC5C312
import HaarC5C336
import HaarC5C360
import HaarC5C384
import HaarC5C408
import HaarC5C432
import HaarC5C456
import HaarC5C480
import HaarC5C504
import HaarC5C528
import HaarC5C552
import HaarC5C576
import HaarC5C600
import HaarC5C624
import HaarC5C648
import HaarC5C672
import HaarC5C696
import HaarC5C720
import HaarC5C744
import HaarC5C768
import HaarC5C792
import HaarC5C816
import HaarC5C840
import HaarC5C864
import HaarC5C888
import HaarC5C912
import HaarC5C936
import HaarC5C960
import HaarC5C984
import HaarC5C1008
import HaarC5C1032
import HaarC5C1056
import HaarC5C1080
import HaarC5C1104
import HaarC5C1128
import HaarC5C1152
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 1157) : valid D i := by
  by_cases h0_49 : i < 576
  · by_cases h0_24 : i < 288
    · by_cases h0_12 : i < 144
      · by_cases h0_6 : i < 72
        · by_cases h0_3 : i < 24
          · exact C000valid i (by omega) (by omega)
          · by_cases h1_3 : i < 48
            · exact C024valid i (by omega) (by omega)
            · exact C048valid i (by omega) (by omega)
        · by_cases h3_6 : i < 96
          · exact C072valid i (by omega) (by omega)
          · by_cases h4_6 : i < 120
            · exact C096valid i (by omega) (by omega)
            · exact C120valid i (by omega) (by omega)
      · by_cases h6_12 : i < 216
        · by_cases h6_9 : i < 168
          · exact C144valid i (by omega) (by omega)
          · by_cases h7_9 : i < 192
            · exact C168valid i (by omega) (by omega)
            · exact C192valid i (by omega) (by omega)
        · by_cases h9_12 : i < 240
          · exact C216valid i (by omega) (by omega)
          · by_cases h10_12 : i < 264
            · exact C240valid i (by omega) (by omega)
            · exact C264valid i (by omega) (by omega)
    · by_cases h12_24 : i < 432
      · by_cases h12_18 : i < 360
        · by_cases h12_15 : i < 312
          · exact C288valid i (by omega) (by omega)
          · by_cases h13_15 : i < 336
            · exact C312valid i (by omega) (by omega)
            · exact C336valid i (by omega) (by omega)
        · by_cases h15_18 : i < 384
          · exact C360valid i (by omega) (by omega)
          · by_cases h16_18 : i < 408
            · exact C384valid i (by omega) (by omega)
            · exact C408valid i (by omega) (by omega)
      · by_cases h18_24 : i < 504
        · by_cases h18_21 : i < 456
          · exact C432valid i (by omega) (by omega)
          · by_cases h19_21 : i < 480
            · exact C456valid i (by omega) (by omega)
            · exact C480valid i (by omega) (by omega)
        · by_cases h21_24 : i < 528
          · exact C504valid i (by omega) (by omega)
          · by_cases h22_24 : i < 552
            · exact C528valid i (by omega) (by omega)
            · exact C552valid i (by omega) (by omega)
  · by_cases h24_49 : i < 864
    · by_cases h24_36 : i < 720
      · by_cases h24_30 : i < 648
        · by_cases h24_27 : i < 600
          · exact C576valid i (by omega) (by omega)
          · by_cases h25_27 : i < 624
            · exact C600valid i (by omega) (by omega)
            · exact C624valid i (by omega) (by omega)
        · by_cases h27_30 : i < 672
          · exact C648valid i (by omega) (by omega)
          · by_cases h28_30 : i < 696
            · exact C672valid i (by omega) (by omega)
            · exact C696valid i (by omega) (by omega)
      · by_cases h30_36 : i < 792
        · by_cases h30_33 : i < 744
          · exact C720valid i (by omega) (by omega)
          · by_cases h31_33 : i < 768
            · exact C744valid i (by omega) (by omega)
            · exact C768valid i (by omega) (by omega)
        · by_cases h33_36 : i < 816
          · exact C792valid i (by omega) (by omega)
          · by_cases h34_36 : i < 840
            · exact C816valid i (by omega) (by omega)
            · exact C840valid i (by omega) (by omega)
    · by_cases h36_49 : i < 1008
      · by_cases h36_42 : i < 936
        · by_cases h36_39 : i < 888
          · exact C864valid i (by omega) (by omega)
          · by_cases h37_39 : i < 912
            · exact C888valid i (by omega) (by omega)
            · exact C912valid i (by omega) (by omega)
        · by_cases h39_42 : i < 960
          · exact C936valid i (by omega) (by omega)
          · by_cases h40_42 : i < 984
            · exact C960valid i (by omega) (by omega)
            · exact C984valid i (by omega) (by omega)
      · by_cases h42_49 : i < 1080
        · by_cases h42_45 : i < 1032
          · exact C1008valid i (by omega) (by omega)
          · by_cases h43_45 : i < 1056
            · exact C1032valid i (by omega) (by omega)
            · exact C1056valid i (by omega) (by omega)
        · by_cases h45_49 : i < 1128
          · by_cases h45_47 : i < 1104
            · exact C1080valid i (by omega) (by omega)
            · exact C1104valid i (by omega) (by omega)
          · by_cases h47_49 : i < 1152
            · exact C1128valid i (by omega) (by omega)
            · exact C1152valid i (by omega) (by omega)
theorem root_empty : (D 1157).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 1157 complete root_empty
end HaarC5Data
#print axioms HaarC5Data.any_voltage
