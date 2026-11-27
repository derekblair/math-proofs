import HeawoodCertCore
namespace HeawoodCert
open HaarOrbitC7Voltage
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def row6 : Data := ⟨2, [2, 1, 0, 2, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 0], ![1,0,1,-1,1,-1,0,1], [![-1,0,0,0,-1,1,0,-1],![0,0,-1,1,-1,1,1,-1]]⟩
theorem check6 : check row6 := by decide +kernel
def row7 : Data := ⟨0, [0, 1, 0, 2, 1, 2, 0, 1], ![0,1,0,0,0,0,0,1], []⟩
theorem check7 : check row7 := by decide +kernel
def row8 : Data := ⟨0, [0, 2, 1, 2, 0, 1, 0, 1], ![0,0,0,1,0,0,0,0], []⟩
theorem check8 : check row8 := by decide +kernel
def row9 : Data := ⟨0, [0, 2, 0, 2, 1, 0, 1, 2], ![1,0,1,0,0,0,0,0], []⟩
theorem check9 : check row9 := by decide +kernel
def row10 : Data := ⟨1, [1, 0, 2, 0, 1, 2, 1, 2], ![0,1,0,0,-1,1,0,0], []⟩
theorem check10 : check row10 := by decide +kernel
end HeawoodCert
