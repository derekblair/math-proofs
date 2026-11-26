import HeawoodCertCore
namespace HeawoodCert
open HaarOrbitC7Voltage
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def row11 : Data := ⟨0, [0, 2, 0, 1, 2, 1, 2, 1], ![0,-1,1,0,0,-1,0,0], []⟩
theorem check11 : check row11 := by decide +kernel
def row12 : Data := ⟨1, [2, 0, 2, 0, 1, 2, 1, 2, 1, 2, 1, 0, 2, 0, 2, 0], ![0,1,-1,0,-1,1,0,0], [![0,-1,0,0,1,-1,0,0],![0,-1,1,0,0,-1,0,0]]⟩
theorem check12 : check row12 := by decide +kernel
def row13 : Data := ⟨0, [0, 2, 0, 2, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 2], ![2,0,2,0,0,0,0,0], [![-1,0,-1,0,0,0,0,0]]⟩
theorem check13 : check row13 := by decide +kernel
def row14 : Data := ⟨0, [2, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1], ![-2,0,-1,0,0,-1,-1,1], [![-1,0,-1,0,0,0,0,0]]⟩
theorem check14 : check row14 := by decide +kernel
def row15 : Data := ⟨0, [1, 2, 1, 0, 2, 0, 1, 2], ![1,0,0,0,0,1,1,-1], []⟩
theorem check15 : check row15 := by decide +kernel
end HeawoodCert
