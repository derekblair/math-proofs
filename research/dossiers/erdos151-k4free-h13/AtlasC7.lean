import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def certC7 : Array Nat := #[21, 21, 42, 0, 21, 21, 0, 0, 41, 41, 42, 0, 0, 0, 0, 0, 21, 21, 82, 0, 21, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 37, 42, 0, 37, 37, 0, 0, 41, 41, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 0, 74, 0, 84, 0, 0, 0, 74, 0, 74, 0, 0, 0, 0, 0, 82, 0, 82, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem blockC7 : ∀ p ∈ List.range 128, !good7 p || cutCheck (make7 p) certC7[p]! = true := by decide +kernel
end BikovEight
