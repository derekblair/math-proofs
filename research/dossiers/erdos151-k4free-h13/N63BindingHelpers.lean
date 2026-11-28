import N63ArithmeticCode
import N63FastCode
import N63TableCore
namespace Erdos151N63
theorem mem_of_mem_slice {α : Type*} {e : α} {L : List α} {off len : Nat}
    (h : e ∈ (L.drop off).take len) : e ∈ L :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)
end Erdos151N63
