import HaarK33C000
import HaarK33C016
import HaarK33C032
import HaarK33C048
import HaarK33C064
import HaarK33C080
import HaarK33C096
import HaarK33C112
import HaarK33C128
import HaarK33C144
import HaarK33C160
import HaarK33C176
import HaarK33C192
import HaarK33C208
import HaarK33C224
import HaarK33C240
import HaarK33C256
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 258) : valid D i := by
  by_cases h0_17 : i < 128
  · by_cases h0_8 : i < 64
    · by_cases h0_4 : i < 32
      · by_cases h0_2 : i < 16
        · exact C000valid i (by omega) (by omega)
        · exact C016valid i (by omega) (by omega)
      · by_cases h2_4 : i < 48
        · exact C032valid i (by omega) (by omega)
        · exact C048valid i (by omega) (by omega)
    · by_cases h4_8 : i < 96
      · by_cases h4_6 : i < 80
        · exact C064valid i (by omega) (by omega)
        · exact C080valid i (by omega) (by omega)
      · by_cases h6_8 : i < 112
        · exact C096valid i (by omega) (by omega)
        · exact C112valid i (by omega) (by omega)
  · by_cases h8_17 : i < 192
    · by_cases h8_12 : i < 160
      · by_cases h8_10 : i < 144
        · exact C128valid i (by omega) (by omega)
        · exact C144valid i (by omega) (by omega)
      · by_cases h10_12 : i < 176
        · exact C160valid i (by omega) (by omega)
        · exact C176valid i (by omega) (by omega)
    · by_cases h12_17 : i < 224
      · by_cases h12_14 : i < 208
        · exact C192valid i (by omega) (by omega)
        · exact C208valid i (by omega) (by omega)
      · by_cases h14_17 : i < 240
        · exact C224valid i (by omega) (by omega)
        · by_cases h15_17 : i < 256
          · exact C240valid i (by omega) (by omega)
          · exact C256valid i (by omega) (by omega)
theorem root_empty : (D 258).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 258 complete root_empty
end HaarK33Data
#print axioms HaarK33Data.any_voltage
