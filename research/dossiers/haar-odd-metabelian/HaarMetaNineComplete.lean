import HaarMetaNineC000
import HaarMetaNineC032
import HaarMetaNineC064
import HaarMetaNineC096
import HaarMetaNineC128
import HaarMetaNineC160
import HaarMetaNineC192
import HaarMetaNineC224
import HaarMetaNineC256
import HaarMetaNineC288
import HaarMetaNineC320
import HaarMetaNineC352
import HaarMetaNineC384
import HaarMetaNineC416
import HaarMetaNineC448
import HaarMetaNineC480
import HaarMetaNineC512
import HaarMetaNineC544
import HaarMetaNineC576
import HaarMetaNineC608
import HaarMetaNineC640
import HaarMetaNineC672
import HaarMetaNineC704
import HaarMetaNineC736
import HaarMetaNineC768
import HaarMetaNineC800
import HaarMetaNineC832
import HaarMetaNineC864
import HaarMetaNineC896
import HaarMetaNineC928
import HaarMetaNineC960
import HaarMetaNineC992
import HaarMetaNineC1024
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 1024) : valid D i := by
  by_cases h0_33 : i < 512
  · by_cases h0_16 : i < 256
    · by_cases h0_8 : i < 128
      · by_cases h0_4 : i < 64
        · by_cases h0_2 : i < 32
          · exact C000valid i (by omega) (by omega)
          · exact C032valid i (by omega) (by omega)
        · by_cases h2_4 : i < 96
          · exact C064valid i (by omega) (by omega)
          · exact C096valid i (by omega) (by omega)
      · by_cases h4_8 : i < 192
        · by_cases h4_6 : i < 160
          · exact C128valid i (by omega) (by omega)
          · exact C160valid i (by omega) (by omega)
        · by_cases h6_8 : i < 224
          · exact C192valid i (by omega) (by omega)
          · exact C224valid i (by omega) (by omega)
    · by_cases h8_16 : i < 384
      · by_cases h8_12 : i < 320
        · by_cases h8_10 : i < 288
          · exact C256valid i (by omega) (by omega)
          · exact C288valid i (by omega) (by omega)
        · by_cases h10_12 : i < 352
          · exact C320valid i (by omega) (by omega)
          · exact C352valid i (by omega) (by omega)
      · by_cases h12_16 : i < 448
        · by_cases h12_14 : i < 416
          · exact C384valid i (by omega) (by omega)
          · exact C416valid i (by omega) (by omega)
        · by_cases h14_16 : i < 480
          · exact C448valid i (by omega) (by omega)
          · exact C480valid i (by omega) (by omega)
  · by_cases h16_33 : i < 768
    · by_cases h16_24 : i < 640
      · by_cases h16_20 : i < 576
        · by_cases h16_18 : i < 544
          · exact C512valid i (by omega) (by omega)
          · exact C544valid i (by omega) (by omega)
        · by_cases h18_20 : i < 608
          · exact C576valid i (by omega) (by omega)
          · exact C608valid i (by omega) (by omega)
      · by_cases h20_24 : i < 704
        · by_cases h20_22 : i < 672
          · exact C640valid i (by omega) (by omega)
          · exact C672valid i (by omega) (by omega)
        · by_cases h22_24 : i < 736
          · exact C704valid i (by omega) (by omega)
          · exact C736valid i (by omega) (by omega)
    · by_cases h24_33 : i < 896
      · by_cases h24_28 : i < 832
        · by_cases h24_26 : i < 800
          · exact C768valid i (by omega) (by omega)
          · exact C800valid i (by omega) (by omega)
        · by_cases h26_28 : i < 864
          · exact C832valid i (by omega) (by omega)
          · exact C864valid i (by omega) (by omega)
      · by_cases h28_33 : i < 960
        · by_cases h28_30 : i < 928
          · exact C896valid i (by omega) (by omega)
          · exact C928valid i (by omega) (by omega)
        · by_cases h30_33 : i < 992
          · exact C960valid i (by omega) (by omega)
          · by_cases h31_33 : i < 1024
            · exact C992valid i (by omega) (by omega)
            · exact C1024valid i (by omega) (by omega)
theorem root_empty : (D 1024).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 1024 complete root_empty
end HaarMetaNineData
#print axioms HaarMetaNineData.any_voltage
