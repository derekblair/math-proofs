import HaarMetaTorusC000
import HaarMetaTorusC032
import HaarMetaTorusC064
import HaarMetaTorusC096
import HaarMetaTorusC128
import HaarMetaTorusC160
import HaarMetaTorusC192
import HaarMetaTorusC224
import HaarMetaTorusC256
import HaarMetaTorusC288
import HaarMetaTorusC320
import HaarMetaTorusC352
import HaarMetaTorusC384
import HaarMetaTorusC416
import HaarMetaTorusC448
import HaarMetaTorusC480
import HaarMetaTorusC512
import HaarMetaTorusC544
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem complete (i : Nat) (_hi : i ≤ 546) : valid D i := by
  by_cases h0_18 : i < 288
  · by_cases h0_9 : i < 128
    · by_cases h0_4 : i < 64
      · by_cases h0_2 : i < 32
        · exact C000valid i (by omega) (by omega)
        · exact C032valid i (by omega) (by omega)
      · by_cases h2_4 : i < 96
        · exact C064valid i (by omega) (by omega)
        · exact C096valid i (by omega) (by omega)
    · by_cases h4_9 : i < 192
      · by_cases h4_6 : i < 160
        · exact C128valid i (by omega) (by omega)
        · exact C160valid i (by omega) (by omega)
      · by_cases h6_9 : i < 224
        · exact C192valid i (by omega) (by omega)
        · by_cases h7_9 : i < 256
          · exact C224valid i (by omega) (by omega)
          · exact C256valid i (by omega) (by omega)
  · by_cases h9_18 : i < 416
    · by_cases h9_13 : i < 352
      · by_cases h9_11 : i < 320
        · exact C288valid i (by omega) (by omega)
        · exact C320valid i (by omega) (by omega)
      · by_cases h11_13 : i < 384
        · exact C352valid i (by omega) (by omega)
        · exact C384valid i (by omega) (by omega)
    · by_cases h13_18 : i < 480
      · by_cases h13_15 : i < 448
        · exact C416valid i (by omega) (by omega)
        · exact C448valid i (by omega) (by omega)
      · by_cases h15_18 : i < 512
        · exact C480valid i (by omega) (by omega)
        · by_cases h16_18 : i < 544
          · exact C512valid i (by omega) (by omega)
          · exact C544valid i (by omega) (by omega)
theorem root_empty : (D 546).rels = [] := by decide +kernel
variable {A : Type*} [AddCommGroup A]
theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=
  dag_sound φ noTwo D 546 complete root_empty
end HaarMetaTorusData
#print axioms HaarMetaTorusData.any_voltage
