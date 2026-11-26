import HeawoodCertCore
namespace HeawoodCert
open HaarOrbitC7Voltage
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def row16 : Data := ⟨1, [1, 2, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 0, 1, 0], ![-1,0,-1,0,0,-1,-1,1], [![-1,0,-1,0,0,0,0,0],![-1,0,0,0,0,-1,-1,1]]⟩
theorem check16 : check row16 := by decide +kernel
def row17 : Data := ⟨0, [0, 2, 1, 0, 1, 2, 0, 2], ![0,0,0,1,-1,1,0,0], []⟩
theorem check17 : check row17 := by decide +kernel
def row18 : Data := ⟨2, [1, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 2], ![0,0,-1,0,1,-1,0,0], [![-1,0,-1,0,0,0,0,0],![0,0,0,-1,1,-1,0,0]]⟩
theorem check18 : check row18 := by decide +kernel
def row19 : Data := ⟨2, [2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 2, 1, 0, 1, 0], ![1,0,-1,1,-1,1,1,-1], [![-1,0,1,-1,0,0,0,0],![0,0,-1,1,-1,1,1,-1]]⟩
theorem check19 : check row19 := by decide +kernel
def row20 : Data := ⟨0, [1, 0, 1, 2, 0, 2, 0, 2], ![0,0,0,0,0,0,-1,1], []⟩
theorem check20 : check row20 := by decide +kernel
end HeawoodCert
