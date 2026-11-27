import HaarMetaS014C000
import HaarMetaS014C024
import HaarMetaS014C048
import HaarMetaS014C072
import HaarMetaS014C096
import HaarMetaS014C120
import HaarMetaS014C144
import HaarMetaS014C168
import HaarMetaS014C192
import HaarMetaS014C216
import HaarMetaS014C240
import HaarMetaS014C264
import HaarMetaS014C288
import HaarMetaS014C312
import HaarMetaS014C336
import HaarMetaS014C360
import HaarMetaS014C384
import HaarMetaS014C408
import HaarMetaS014C432
import HaarMetaS014C456
import HaarMetaS014C480
import HaarMetaS014C504
import HaarMetaS014C528
import HaarMetaS014C552
import HaarMetaS014C576
import HaarMetaS014C600
import HaarMetaS014C624
namespace HaarMetaS014Data
open HaarMetaS014DAG HaarMetaS014Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 645) : valid D i := by
  by_cases h0_27 : i < 312
  · by_cases h0_13 : i < 144
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
    · by_cases h6_13 : i < 216
      · by_cases h6_9 : i < 168
        · exact C144valid i (by omega) (by omega)
        · by_cases h7_9 : i < 192
          · exact C168valid i (by omega) (by omega)
          · exact C192valid i (by omega) (by omega)
      · by_cases h9_13 : i < 264
        · by_cases h9_11 : i < 240
          · exact C216valid i (by omega) (by omega)
          · exact C240valid i (by omega) (by omega)
        · by_cases h11_13 : i < 288
          · exact C264valid i (by omega) (by omega)
          · exact C288valid i (by omega) (by omega)
  · by_cases h13_27 : i < 480
    · by_cases h13_20 : i < 384
      · by_cases h13_16 : i < 336
        · exact C312valid i (by omega) (by omega)
        · by_cases h14_16 : i < 360
          · exact C336valid i (by omega) (by omega)
          · exact C360valid i (by omega) (by omega)
      · by_cases h16_20 : i < 432
        · by_cases h16_18 : i < 408
          · exact C384valid i (by omega) (by omega)
          · exact C408valid i (by omega) (by omega)
        · by_cases h18_20 : i < 456
          · exact C432valid i (by omega) (by omega)
          · exact C456valid i (by omega) (by omega)
    · by_cases h20_27 : i < 552
      · by_cases h20_23 : i < 504
        · exact C480valid i (by omega) (by omega)
        · by_cases h21_23 : i < 528
          · exact C504valid i (by omega) (by omega)
          · exact C528valid i (by omega) (by omega)
      · by_cases h23_27 : i < 600
        · by_cases h23_25 : i < 576
          · exact C552valid i (by omega) (by omega)
          · exact C576valid i (by omega) (by omega)
        · by_cases h25_27 : i < 624
          · exact C600valid i (by omega) (by omega)
          · exact C624valid i (by omega) (by omega)
theorem root_empty : (D 645).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 645 complete root_empty
end HaarMetaS014Data
#print axioms HaarMetaS014Data.any_voltage
