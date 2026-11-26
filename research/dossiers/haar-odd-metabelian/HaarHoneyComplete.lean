import HaarHoneyC000
import HaarHoneyC024
import HaarHoneyC048
import HaarHoneyC072
import HaarHoneyC096
import HaarHoneyC120
import HaarHoneyC144
import HaarHoneyC168
import HaarHoneyC192
import HaarHoneyC216
import HaarHoneyC240
import HaarHoneyC264
import HaarHoneyC288
import HaarHoneyC312
import HaarHoneyC336
import HaarHoneyC360
import HaarHoneyC384
import HaarHoneyC408
import HaarHoneyC432
import HaarHoneyC456
import HaarHoneyC480
import HaarHoneyC504
import HaarHoneyC528
import HaarHoneyC552
import HaarHoneyC576
import HaarHoneyC600
import HaarHoneyC624
import HaarHoneyC648
import HaarHoneyC672
import HaarHoneyC696
import HaarHoneyC720
import HaarHoneyC744
import HaarHoneyC768
import HaarHoneyC792
import HaarHoneyC816
import HaarHoneyC840
import HaarHoneyC864
import HaarHoneyC888
import HaarHoneyC912
import HaarHoneyC936
import HaarHoneyC960
import HaarHoneyC984
import HaarHoneyC1008
import HaarHoneyC1032
import HaarHoneyC1056
import HaarHoneyC1080
import HaarHoneyC1104
import HaarHoneyC1128
import HaarHoneyC1152
import HaarHoneyC1176
import HaarHoneyC1200
import HaarHoneyC1224
import HaarHoneyC1248
import HaarHoneyC1272
import HaarHoneyC1296
import HaarHoneyC1320
import HaarHoneyC1344
import HaarHoneyC1368
import HaarHoneyC1392
import HaarHoneyC1416
import HaarHoneyC1440
import HaarHoneyC1464
import HaarHoneyC1488
import HaarHoneyC1512
import HaarHoneyC1536
import HaarHoneyC1560
import HaarHoneyC1584
import HaarHoneyC1608
import HaarHoneyC1632
import HaarHoneyC1656
import HaarHoneyC1680
import HaarHoneyC1704
import HaarHoneyC1728
import HaarHoneyC1752
import HaarHoneyC1776
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 1796) : valid D i := by
  by_cases h0_75 : i < 888
  · by_cases h0_37 : i < 432
    · by_cases h0_18 : i < 216
      · by_cases h0_9 : i < 96
        · by_cases h0_4 : i < 48
          · by_cases h0_2 : i < 24
            · exact C000valid i (by omega) (by omega)
            · exact C024valid i (by omega) (by omega)
          · by_cases h2_4 : i < 72
            · exact C048valid i (by omega) (by omega)
            · exact C072valid i (by omega) (by omega)
        · by_cases h4_9 : i < 144
          · by_cases h4_6 : i < 120
            · exact C096valid i (by omega) (by omega)
            · exact C120valid i (by omega) (by omega)
          · by_cases h6_9 : i < 168
            · exact C144valid i (by omega) (by omega)
            · by_cases h7_9 : i < 192
              · exact C168valid i (by omega) (by omega)
              · exact C192valid i (by omega) (by omega)
      · by_cases h9_18 : i < 312
        · by_cases h9_13 : i < 264
          · by_cases h9_11 : i < 240
            · exact C216valid i (by omega) (by omega)
            · exact C240valid i (by omega) (by omega)
          · by_cases h11_13 : i < 288
            · exact C264valid i (by omega) (by omega)
            · exact C288valid i (by omega) (by omega)
        · by_cases h13_18 : i < 360
          · by_cases h13_15 : i < 336
            · exact C312valid i (by omega) (by omega)
            · exact C336valid i (by omega) (by omega)
          · by_cases h15_18 : i < 384
            · exact C360valid i (by omega) (by omega)
            · by_cases h16_18 : i < 408
              · exact C384valid i (by omega) (by omega)
              · exact C408valid i (by omega) (by omega)
    · by_cases h18_37 : i < 648
      · by_cases h18_27 : i < 528
        · by_cases h18_22 : i < 480
          · by_cases h18_20 : i < 456
            · exact C432valid i (by omega) (by omega)
            · exact C456valid i (by omega) (by omega)
          · by_cases h20_22 : i < 504
            · exact C480valid i (by omega) (by omega)
            · exact C504valid i (by omega) (by omega)
        · by_cases h22_27 : i < 576
          · by_cases h22_24 : i < 552
            · exact C528valid i (by omega) (by omega)
            · exact C552valid i (by omega) (by omega)
          · by_cases h24_27 : i < 600
            · exact C576valid i (by omega) (by omega)
            · by_cases h25_27 : i < 624
              · exact C600valid i (by omega) (by omega)
              · exact C624valid i (by omega) (by omega)
      · by_cases h27_37 : i < 768
        · by_cases h27_32 : i < 696
          · by_cases h27_29 : i < 672
            · exact C648valid i (by omega) (by omega)
            · exact C672valid i (by omega) (by omega)
          · by_cases h29_32 : i < 720
            · exact C696valid i (by omega) (by omega)
            · by_cases h30_32 : i < 744
              · exact C720valid i (by omega) (by omega)
              · exact C744valid i (by omega) (by omega)
        · by_cases h32_37 : i < 816
          · by_cases h32_34 : i < 792
            · exact C768valid i (by omega) (by omega)
            · exact C792valid i (by omega) (by omega)
          · by_cases h34_37 : i < 840
            · exact C816valid i (by omega) (by omega)
            · by_cases h35_37 : i < 864
              · exact C840valid i (by omega) (by omega)
              · exact C864valid i (by omega) (by omega)
  · by_cases h37_75 : i < 1344
    · by_cases h37_56 : i < 1104
      · by_cases h37_46 : i < 984
        · by_cases h37_41 : i < 936
          · by_cases h37_39 : i < 912
            · exact C888valid i (by omega) (by omega)
            · exact C912valid i (by omega) (by omega)
          · by_cases h39_41 : i < 960
            · exact C936valid i (by omega) (by omega)
            · exact C960valid i (by omega) (by omega)
        · by_cases h41_46 : i < 1032
          · by_cases h41_43 : i < 1008
            · exact C984valid i (by omega) (by omega)
            · exact C1008valid i (by omega) (by omega)
          · by_cases h43_46 : i < 1056
            · exact C1032valid i (by omega) (by omega)
            · by_cases h44_46 : i < 1080
              · exact C1056valid i (by omega) (by omega)
              · exact C1080valid i (by omega) (by omega)
      · by_cases h46_56 : i < 1224
        · by_cases h46_51 : i < 1152
          · by_cases h46_48 : i < 1128
            · exact C1104valid i (by omega) (by omega)
            · exact C1128valid i (by omega) (by omega)
          · by_cases h48_51 : i < 1176
            · exact C1152valid i (by omega) (by omega)
            · by_cases h49_51 : i < 1200
              · exact C1176valid i (by omega) (by omega)
              · exact C1200valid i (by omega) (by omega)
        · by_cases h51_56 : i < 1272
          · by_cases h51_53 : i < 1248
            · exact C1224valid i (by omega) (by omega)
            · exact C1248valid i (by omega) (by omega)
          · by_cases h53_56 : i < 1296
            · exact C1272valid i (by omega) (by omega)
            · by_cases h54_56 : i < 1320
              · exact C1296valid i (by omega) (by omega)
              · exact C1320valid i (by omega) (by omega)
    · by_cases h56_75 : i < 1560
      · by_cases h56_65 : i < 1440
        · by_cases h56_60 : i < 1392
          · by_cases h56_58 : i < 1368
            · exact C1344valid i (by omega) (by omega)
            · exact C1368valid i (by omega) (by omega)
          · by_cases h58_60 : i < 1416
            · exact C1392valid i (by omega) (by omega)
            · exact C1416valid i (by omega) (by omega)
        · by_cases h60_65 : i < 1488
          · by_cases h60_62 : i < 1464
            · exact C1440valid i (by omega) (by omega)
            · exact C1464valid i (by omega) (by omega)
          · by_cases h62_65 : i < 1512
            · exact C1488valid i (by omega) (by omega)
            · by_cases h63_65 : i < 1536
              · exact C1512valid i (by omega) (by omega)
              · exact C1536valid i (by omega) (by omega)
      · by_cases h65_75 : i < 1680
        · by_cases h65_70 : i < 1608
          · by_cases h65_67 : i < 1584
            · exact C1560valid i (by omega) (by omega)
            · exact C1584valid i (by omega) (by omega)
          · by_cases h67_70 : i < 1632
            · exact C1608valid i (by omega) (by omega)
            · by_cases h68_70 : i < 1656
              · exact C1632valid i (by omega) (by omega)
              · exact C1656valid i (by omega) (by omega)
        · by_cases h70_75 : i < 1728
          · by_cases h70_72 : i < 1704
            · exact C1680valid i (by omega) (by omega)
            · exact C1704valid i (by omega) (by omega)
          · by_cases h72_75 : i < 1752
            · exact C1728valid i (by omega) (by omega)
            · by_cases h73_75 : i < 1776
              · exact C1752valid i (by omega) (by omega)
              · exact C1776valid i (by omega) (by omega)
theorem root_empty : (D 1796).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 1796 complete root_empty
end HaarHoneyData
#print axioms HaarHoneyData.any_voltage
