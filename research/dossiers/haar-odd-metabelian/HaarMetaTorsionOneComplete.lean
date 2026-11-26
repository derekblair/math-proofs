import HaarMetaTorsionOneC000
import HaarMetaTorsionOneC024
import HaarMetaTorsionOneC048
import HaarMetaTorsionOneC072
import HaarMetaTorsionOneC096
import HaarMetaTorsionOneC120
import HaarMetaTorsionOneC144
import HaarMetaTorsionOneC168
import HaarMetaTorsionOneC192
import HaarMetaTorsionOneC216
import HaarMetaTorsionOneC240
import HaarMetaTorsionOneC264
import HaarMetaTorsionOneC288
import HaarMetaTorsionOneC312
import HaarMetaTorsionOneC336
import HaarMetaTorsionOneC360
import HaarMetaTorsionOneC384
import HaarMetaTorsionOneC408
import HaarMetaTorsionOneC432
import HaarMetaTorsionOneC456
import HaarMetaTorsionOneC480
import HaarMetaTorsionOneC504
import HaarMetaTorsionOneC528
import HaarMetaTorsionOneC552
import HaarMetaTorsionOneC576
import HaarMetaTorsionOneC600
import HaarMetaTorsionOneC624
import HaarMetaTorsionOneC648
import HaarMetaTorsionOneC672
import HaarMetaTorsionOneC696
import HaarMetaTorsionOneC720
import HaarMetaTorsionOneC744
import HaarMetaTorsionOneC768
import HaarMetaTorsionOneC792
import HaarMetaTorsionOneC816
import HaarMetaTorsionOneC840
import HaarMetaTorsionOneC864
import HaarMetaTorsionOneC888
import HaarMetaTorsionOneC912
import HaarMetaTorsionOneC936
import HaarMetaTorsionOneC960
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 963) : valid D i := by
  by_cases h0_41 : i < 480
  · by_cases h0_20 : i < 240
    · by_cases h0_10 : i < 120
      · by_cases h0_5 : i < 48
        · by_cases h0_2 : i < 24
          · exact C000valid i (by omega) (by omega)
          · exact C024valid i (by omega) (by omega)
        · by_cases h2_5 : i < 72
          · exact C048valid i (by omega) (by omega)
          · by_cases h3_5 : i < 96
            · exact C072valid i (by omega) (by omega)
            · exact C096valid i (by omega) (by omega)
      · by_cases h5_10 : i < 168
        · by_cases h5_7 : i < 144
          · exact C120valid i (by omega) (by omega)
          · exact C144valid i (by omega) (by omega)
        · by_cases h7_10 : i < 192
          · exact C168valid i (by omega) (by omega)
          · by_cases h8_10 : i < 216
            · exact C192valid i (by omega) (by omega)
            · exact C216valid i (by omega) (by omega)
    · by_cases h10_20 : i < 360
      · by_cases h10_15 : i < 288
        · by_cases h10_12 : i < 264
          · exact C240valid i (by omega) (by omega)
          · exact C264valid i (by omega) (by omega)
        · by_cases h12_15 : i < 312
          · exact C288valid i (by omega) (by omega)
          · by_cases h13_15 : i < 336
            · exact C312valid i (by omega) (by omega)
            · exact C336valid i (by omega) (by omega)
      · by_cases h15_20 : i < 408
        · by_cases h15_17 : i < 384
          · exact C360valid i (by omega) (by omega)
          · exact C384valid i (by omega) (by omega)
        · by_cases h17_20 : i < 432
          · exact C408valid i (by omega) (by omega)
          · by_cases h18_20 : i < 456
            · exact C432valid i (by omega) (by omega)
            · exact C456valid i (by omega) (by omega)
  · by_cases h20_41 : i < 720
    · by_cases h20_30 : i < 600
      · by_cases h20_25 : i < 528
        · by_cases h20_22 : i < 504
          · exact C480valid i (by omega) (by omega)
          · exact C504valid i (by omega) (by omega)
        · by_cases h22_25 : i < 552
          · exact C528valid i (by omega) (by omega)
          · by_cases h23_25 : i < 576
            · exact C552valid i (by omega) (by omega)
            · exact C576valid i (by omega) (by omega)
      · by_cases h25_30 : i < 648
        · by_cases h25_27 : i < 624
          · exact C600valid i (by omega) (by omega)
          · exact C624valid i (by omega) (by omega)
        · by_cases h27_30 : i < 672
          · exact C648valid i (by omega) (by omega)
          · by_cases h28_30 : i < 696
            · exact C672valid i (by omega) (by omega)
            · exact C696valid i (by omega) (by omega)
    · by_cases h30_41 : i < 840
      · by_cases h30_35 : i < 768
        · by_cases h30_32 : i < 744
          · exact C720valid i (by omega) (by omega)
          · exact C744valid i (by omega) (by omega)
        · by_cases h32_35 : i < 792
          · exact C768valid i (by omega) (by omega)
          · by_cases h33_35 : i < 816
            · exact C792valid i (by omega) (by omega)
            · exact C816valid i (by omega) (by omega)
      · by_cases h35_41 : i < 912
        · by_cases h35_38 : i < 864
          · exact C840valid i (by omega) (by omega)
          · by_cases h36_38 : i < 888
            · exact C864valid i (by omega) (by omega)
            · exact C888valid i (by omega) (by omega)
        · by_cases h38_41 : i < 936
          · exact C912valid i (by omega) (by omega)
          · by_cases h39_41 : i < 960
            · exact C936valid i (by omega) (by omega)
            · exact C960valid i (by omega) (by omega)
theorem root_empty : (D 963).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 963 complete root_empty
end HaarMetaTorsionOneData
#print axioms HaarMetaTorsionOneData.any_voltage
