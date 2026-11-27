import HeawoodCertCore
namespace HeawoodCert
open HaarOrbitC7Voltage
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def row31 : Data := ⟨0, [1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0], ![0,0,0,0,0,0,0,0], [![-1,0,-2,0,0,0,0,0],![-1,0,-1,0,0,0,0,0],![-1,0,0,0,0,0,0,0],![-1,0,1,0,0,0,0,0],![0,0,-2,0,0,0,0,0],![0,0,-1,0,0,0,0,0]]⟩
theorem check31 : check row31 := by decide +kernel
end HeawoodCert
