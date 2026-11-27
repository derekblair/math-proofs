import HaarMetaS013C000
import HaarMetaS013C024
import HaarMetaS013C048
import HaarMetaS013C072
import HaarMetaS013C096
namespace HaarMetaS013Data
open HaarMetaS013DAG HaarMetaS013Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 109) : valid D i := by
  by_cases h0_5 : i < 48
  · by_cases h0_2 : i < 24
    · exact C000valid i (by omega) (by omega)
    · exact C024valid i (by omega) (by omega)
  · by_cases h2_5 : i < 72
    · exact C048valid i (by omega) (by omega)
    · by_cases h3_5 : i < 96
      · exact C072valid i (by omega) (by omega)
      · exact C096valid i (by omega) (by omega)
theorem root_empty : (D 109).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 109 complete root_empty
end HaarMetaS013Data
#print axioms HaarMetaS013Data.any_voltage
