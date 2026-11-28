import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert64 : Array Nat := #[52, 0, 52, 0, 0, 52, 52, 0, 0, 37, 69, 37, 69, 37, 37, 69, 77, 37, 37, 85, 37, 0, 37, 34512944, 37, 37, 0, 0, 37, 37, 5447657, 69]
theorem block64 : ∀ u ∈ List.range 32, !valid5 (2048+u) || check (word5 (2048+u)) cert64[u]! = true := by decide +kernel
def cert65 : Array Nat := #[69, 0, 69, 77, 85, 69, 77, 0, 0, 85, 37, 5414896, 37, 0, 37, 37, 0, 34545705, 37, 37, 0, 45, 69, 45, 69, 0, 45, 69, 0, 0, 45, 85]
theorem block65 : ∀ u ∈ List.range 32, !valid5 (2080+u) || check (word5 (2080+u)) cert65[u]! = true := by decide +kernel
def cert66 : Array Nat := #[53, 69, 53, 69, 53, 0, 69, 77, 53, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 45, 0, 45, 34512945, 0, 45, 0, 0, 0, 45]
theorem block66 : ∀ u ∈ List.range 32, !valid5 (2112+u) || check (word5 (2112+u)) cert66[u]! = true := by decide +kernel
def cert67 : Array Nat := #[34512946, 69, 69, 0, 69, 0, 85, 69, 0, 0, 0, 85, 69, 69, 0, 69, 77, 0, 69, 77, 0, 0, 0, 53, 5414897, 53, 0, 53, 0, 0, 5414898, 53]
theorem block67 : ∀ u ∈ List.range 32, !valid5 (2144+u) || check (word5 (2144+u)) cert67[u]! = true := by decide +kernel
def cert68 : Array Nat := #[0, 0, 41, 73, 41, 41, 73, 41, 77, 73, 75, 41, 41, 41, 0, 41, 41, 51040112, 41, 0, 0, 6770601, 41, 41, 43, 73, 0, 43, 73, 43, 77, 73]
theorem block68 : ∀ u ∈ List.range 32, !valid5 (2176+u) || check (word5 (2176+u)) cert68[u]! = true := by decide +kernel
def cert69 : Array Nat := #[0, 0, 43, 45, 73, 45, 0, 73, 45, 0, 73, 75, 45, 0, 41, 6737840, 41, 41, 0, 41, 51072873, 0, 0, 41, 41, 73, 73, 75, 77, 73, 0, 77]
theorem block69 : ∀ u ∈ List.range 32, !valid5 (2208+u) || check (word5 (2208+u)) cert69[u]! = true := by decide +kernel
def cert70 : Array Nat := #[73, 75, 0, 0, 45, 0, 45, 0, 51040113, 45, 0, 0, 51040114, 45, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 43, 6737841, 0, 43, 0, 43]
theorem block70 : ∀ u ∈ List.range 32, !valid5 (2240+u) || check (word5 (2240+u)) cert70[u]! = true := by decide +kernel
def cert71 : Array Nat := #[6737842, 0, 0, 0, 43, 73, 73, 0, 77, 73, 0, 77, 73, 0, 0, 0, 73, 73, 75, 0, 73, 0, 0, 73, 75, 0, 0, 42, 42, 74, 42, 74]
theorem block71 : ∀ u ∈ List.range 32, !valid5 (2272+u) || check (word5 (2272+u)) cert71[u]! = true := by decide +kernel

theorem portion8 (h : Nat) (lo : 2048≤h) (hi : h<2304) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t68 : h<2176
  ·
    by_cases t66 : h<2112
    ·
      by_cases t65 : h<2080
      ·
        have H := block64 (h-2048) (List.mem_range.mpr (by omega))
        have E : 2048+(h-2048)=h := by omega
        rw [E,valid] at H
        exact ⟨cert64[h-2048]!,by simpa using H⟩
      ·
        have H := block65 (h-2080) (List.mem_range.mpr (by omega))
        have E : 2080+(h-2080)=h := by omega
        rw [E,valid] at H
        exact ⟨cert65[h-2080]!,by simpa using H⟩
    ·
      by_cases t67 : h<2144
      ·
        have H := block66 (h-2112) (List.mem_range.mpr (by omega))
        have E : 2112+(h-2112)=h := by omega
        rw [E,valid] at H
        exact ⟨cert66[h-2112]!,by simpa using H⟩
      ·
        have H := block67 (h-2144) (List.mem_range.mpr (by omega))
        have E : 2144+(h-2144)=h := by omega
        rw [E,valid] at H
        exact ⟨cert67[h-2144]!,by simpa using H⟩
  ·
    by_cases t70 : h<2240
    ·
      by_cases t69 : h<2208
      ·
        have H := block68 (h-2176) (List.mem_range.mpr (by omega))
        have E : 2176+(h-2176)=h := by omega
        rw [E,valid] at H
        exact ⟨cert68[h-2176]!,by simpa using H⟩
      ·
        have H := block69 (h-2208) (List.mem_range.mpr (by omega))
        have E : 2208+(h-2208)=h := by omega
        rw [E,valid] at H
        exact ⟨cert69[h-2208]!,by simpa using H⟩
    ·
      by_cases t71 : h<2272
      ·
        have H := block70 (h-2240) (List.mem_range.mpr (by omega))
        have E : 2240+(h-2240)=h := by omega
        rw [E,valid] at H
        exact ⟨cert70[h-2240]!,by simpa using H⟩
      ·
        have H := block71 (h-2272) (List.mem_range.mpr (by omega))
        have E : 2272+(h-2272)=h := by omega
        rw [E,valid] at H
        exact ⟨cert71[h-2272]!,by simpa using H⟩
end BikovEight
