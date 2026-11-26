import Ribbon5OwnerFinished
import Ribbon5Component

namespace Ribbon5UT
open Ribbon5Owner

theorem full_endpoint_test : Ribbon5Packed.Checked16 :=
  fun s q r ne => separates ne (allgood s q) (allgood s r)

theorem fully_verified_sharp_component :
    ¬ ComponentCycle 4 ∧ ¬ ComponentCycle 8 ∧ ¬ ComponentCycle 16 ∧
      ¬ ComponentCycle 32 ∧ ComponentCycle 64 :=
  connected_sharp full_endpoint_test

end Ribbon5UT
#print axioms Ribbon5UT.full_endpoint_test
#print axioms Ribbon5UT.fully_verified_sharp_component
