import Color13Part0
import Color13PartBank1
import Color13PartBank5
import Color13PartBank9
import Color13PartBank13
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
def all13 : List (List (List Nat)) := [part0, part1, part2, part3, part4, part5, part6, part7, part8, part9, part10, part11, part12, part13, part14, part15]
def pc13 := all13.flatten
theorem all13_ok : proper 13 2 2 pc13 := by
  apply proper_flatten
  intro c m
  simp only [all13,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact part_ok0
  · exact part_ok1
  · exact part_ok2
  · exact part_ok3
  · exact part_ok4
  · exact part_ok5
  · exact part_ok6
  · exact part_ok7
  · exact part_ok8
  · exact part_ok9
  · exact part_ok10
  · exact part_ok11
  · exact part_ok12
  · exact part_ok13
  · exact part_ok14
  · exact part_ok15

end IU
