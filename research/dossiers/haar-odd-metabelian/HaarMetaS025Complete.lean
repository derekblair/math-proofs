import HaarMetaS025C000
import HaarMetaS025C024
import HaarMetaS025C048
import HaarMetaS025C072
import HaarMetaS025C096
import HaarMetaS025C120
import HaarMetaS025C144
import HaarMetaS025C168
import HaarMetaS025C192
import HaarMetaS025C216
import HaarMetaS025C240
import HaarMetaS025C264
import HaarMetaS025C288
import HaarMetaS025C312
import HaarMetaS025C336
import HaarMetaS025C360
import HaarMetaS025C384
import HaarMetaS025C408
namespace HaarMetaS025Data
open HaarMetaS025DAG HaarMetaS025Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 414) : valid D i := by
  by_cases h0_18 : i < 216
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
theorem root_empty : (D 414).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 414 complete root_empty
end HaarMetaS025Data
#print axioms HaarMetaS025Data.any_voltage
