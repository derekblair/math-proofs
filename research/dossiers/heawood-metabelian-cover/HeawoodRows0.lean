import HeawoodCertCore
namespace HeawoodCert
open HaarOrbitC7Voltage
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def row1 : Data := ⟨0, [1, 0, 2, 0, 1, 2, 1, 2], ![1,0,-1,1,0,0,0,0], []⟩
theorem check1 : check row1 := by decide +kernel
def row2 : Data := ⟨2, [1, 0, 2, 0, 1, 2, 1, 2], ![1,0,0,1,0,0,0,-1], []⟩
theorem check2 : check row2 := by decide +kernel
def row3 : Data := ⟨3, [0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2, 0, 1], ![1,-1,0,1,0,0,0,-1], [![-1,0,0,-1,0,0,0,1],![-1,0,1,-1,0,0,0,0]]⟩
theorem check3 : check row3 := by decide +kernel
def row4 : Data := ⟨0, [0, 1, 0, 1, 0, 2, 1, 2], ![1,0,0,0,1,-1,0,1], []⟩
theorem check4 : check row4 := by decide +kernel
def row5 : Data := ⟨1, [1, 2, 0, 1, 0, 1, 0, 2], ![0,0,1,-1,1,-1,-1,1], []⟩
theorem check5 : check row5 := by decide +kernel
end HeawoodCert
