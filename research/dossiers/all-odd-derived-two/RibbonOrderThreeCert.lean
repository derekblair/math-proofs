import RibbonOrderThreeAff
namespace RibbonOrderThree
open RibbonStationaryWord
set_option maxRecDepth 32000
set_option maxHeartbeats 0
structure Input where
  p : Nat
  a : Nat
  b : Nat
  word : W3
def inputs : Fin 28 → Input := ![⟨7,1,2,0⟩,⟨7,1,4,0⟩,⟨7,2,1,0⟩,⟨7,2,2,0⟩,⟨7,2,4,1⟩,⟨7,4,1,0⟩,⟨7,4,2,1⟩,⟨7,4,4,0⟩,⟨11,1,3,0⟩,⟨11,1,4,0⟩,⟨11,1,5,1⟩,⟨11,1,9,0⟩,⟨11,3,1,0⟩,⟨11,3,3,0⟩,⟨11,3,4,0⟩,⟨11,4,1,0⟩,⟨11,4,3,0⟩,⟨11,4,4,0⟩,⟨11,5,1,2⟩,⟨11,5,5,0⟩,⟨11,5,9,0⟩,⟨11,9,1,0⟩,⟨11,9,5,0⟩,⟨11,9,9,1⟩,⟨13,1,3,0⟩,⟨13,1,9,0⟩,⟨13,3,1,0⟩,⟨13,9,1,0⟩]
def Ok (i : Fin 28) : Prop :=
  let z := inputs i
  RibbonP11Pair.checkRows (lowRow z.word) (affRow z.p z.a z.b (wid z.word)) (spec (wid z.word))=true
instance (i : Fin 28) : Decidable (Ok i) := by unfold Ok; infer_instance
private theorem input0 : Ok 0 := by decide +kernel
private theorem input1 : Ok 1 := by decide +kernel
private theorem input2 : Ok 2 := by decide +kernel
private theorem input3 : Ok 3 := by decide +kernel
private theorem input4 : Ok 4 := by decide +kernel
private theorem input5 : Ok 5 := by decide +kernel
private theorem input6 : Ok 6 := by decide +kernel
private theorem input7 : Ok 7 := by decide +kernel
private theorem input8 : Ok 8 := by decide +kernel
private theorem input9 : Ok 9 := by decide +kernel
private theorem input10 : Ok 10 := by decide +kernel
private theorem input11 : Ok 11 := by decide +kernel
private theorem input12 : Ok 12 := by decide +kernel
private theorem input13 : Ok 13 := by decide +kernel
private theorem input14 : Ok 14 := by decide +kernel
private theorem input15 : Ok 15 := by decide +kernel
private theorem input16 : Ok 16 := by decide +kernel
private theorem input17 : Ok 17 := by decide +kernel
private theorem input18 : Ok 18 := by decide +kernel
private theorem input19 : Ok 19 := by decide +kernel
private theorem input20 : Ok 20 := by decide +kernel
private theorem input21 : Ok 21 := by decide +kernel
private theorem input22 : Ok 22 := by decide +kernel
private theorem input23 : Ok 23 := by decide +kernel
private theorem input24 : Ok 24 := by decide +kernel
private theorem input25 : Ok 25 := by decide +kernel
private theorem input26 : Ok 26 := by decide +kernel
private theorem input27 : Ok 27 := by decide +kernel

theorem all_inputs (i : Fin 28) : Ok i := by
  fin_cases i
  · exact input0
  · exact input1
  · exact input2
  · exact input3
  · exact input4
  · exact input5
  · exact input6
  · exact input7
  · exact input8
  · exact input9
  · exact input10
  · exact input11
  · exact input12
  · exact input13
  · exact input14
  · exact input15
  · exact input16
  · exact input17
  · exact input18
  · exact input19
  · exact input20
  · exact input21
  · exact input22
  · exact input23
  · exact input24
  · exact input25
  · exact input26
  · exact input27

end RibbonOrderThree
#print axioms RibbonOrderThree.all_inputs
