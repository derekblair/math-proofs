import HeawoodCertCore
namespace HeawoodCert
open HaarOrbitC7Voltage
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def row21 : Data := ⟨2, [0, 2, 0, 2, 0, 2, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1], ![-1,0,0,-1,0,0,-1,1], [![0,0,0,-1,0,0,0,0],![0,0,0,0,0,0,-1,1]]⟩
theorem check21 : check row21 := by decide +kernel
def row22 : Data := ⟨4, [1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 2, 0, 1, 0, 2], ![-1,0,1,0,-1,1,0,-1], [![-1,0,0,0,-1,1,0,-1],![-1,0,1,-1,0,0,0,0]]⟩
theorem check22 : check row22 := by decide +kernel
def row23 : Data := ⟨1, [1, 0, 2, 1, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 2], ![0,1,0,-1,-1,1,0,0], [![0,0,0,-1,0,0,0,0]]⟩
theorem check23 : check row23 := by decide +kernel
def row24 : Data := ⟨4, [2, 1, 0, 2, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 0], ![0,1,-1,1,0,0,0,1], [![0,-1,0,0,0,0,0,-1],![0,0,0,-1,0,0,0,0]]⟩
theorem check24 : check row24 := by decide +kernel
def row25 : Data := ⟨0, [1, 0, 1, 0, 2, 1, 2, 1, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0], ![0,0,0,0,0,0,0,0], [![0,-1,0,0,0,0,0,-1],![0,-1,0,0,1,-1,0,0],![0,-1,0,1,0,0,0,-1],![0,-1,1,0,1,-1,0,0],![0,0,-1,0,0,0,0,0],![0,0,-1,1,-1,1,0,-1],![0,0,-1,1,0,0,0,0],![0,0,0,-1,0,0,0,0],![0,0,0,0,-1,1,0,-1]]⟩
theorem check25 : check row25 := by decide +kernel
end HeawoodCert
