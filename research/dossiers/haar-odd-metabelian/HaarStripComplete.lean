import HaarStripC000
import HaarStripC024
import HaarStripC048
import HaarStripC072
import HaarStripC096
import HaarStripC120
import HaarStripC144
import HaarStripC168
import HaarStripC192
import HaarStripC216
import HaarStripC240
import HaarStripC264
import HaarStripC288
import HaarStripC312
namespace HaarStripData
open HaarStripDAG HaarStripVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 334) : valid D i := by
  by_cases h0_14 : i < 168
  · by_cases h0_7 : i < 72
    · by_cases h0_3 : i < 24
      · exact C000valid i (by omega) (by omega)
      · by_cases h1_3 : i < 48
        · exact C024valid i (by omega) (by omega)
        · exact C048valid i (by omega) (by omega)
    · by_cases h3_7 : i < 120
      · by_cases h3_5 : i < 96
        · exact C072valid i (by omega) (by omega)
        · exact C096valid i (by omega) (by omega)
      · by_cases h5_7 : i < 144
        · exact C120valid i (by omega) (by omega)
        · exact C144valid i (by omega) (by omega)
  · by_cases h7_14 : i < 240
    · by_cases h7_10 : i < 192
      · exact C168valid i (by omega) (by omega)
      · by_cases h8_10 : i < 216
        · exact C192valid i (by omega) (by omega)
        · exact C216valid i (by omega) (by omega)
    · by_cases h10_14 : i < 288
      · by_cases h10_12 : i < 264
        · exact C240valid i (by omega) (by omega)
        · exact C264valid i (by omega) (by omega)
      · by_cases h12_14 : i < 312
        · exact C288valid i (by omega) (by omega)
        · exact C312valid i (by omega) (by omega)
theorem root_empty : (D 334).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 334 complete root_empty
end HaarStripData
#print axioms HaarStripData.any_voltage
