import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert24 : Array Nat := #[37, 21, 13, 13, 45, 13, 13, 45, 13, 13, 101, 45, 85, 21, 21, 53, 21, 53, 21, 21, 77, 53, 101, 21, 5, 5, 37, 5, 13, 21, 5, 13]
theorem block24 : ∀ u ∈ List.range 32, !valid5 (768+u) || check (word5 (768+u)) cert24[u]! = true := by decide +kernel
def cert25 : Array Nat := #[37, 37, 21, 13, 13, 45, 13, 13, 45, 13, 13, 6803025, 45, 34513057, 69, 69, 101, 69, 101, 85, 69, 6802577, 101, 101, 85, 69, 69, 101, 69, 77, 101, 69]
theorem block25 : ∀ u ∈ List.range 32, !valid5 (800+u) || check (word5 (800+u)) cert25[u]! = true := by decide +kernel
def cert26 : Array Nat := #[77, 101, 101, 71515337, 21, 21, 53, 21, 53, 21, 21, 34545761, 53, 71483081, 21, 9, 9, 11, 13, 9, 41, 13, 9, 11, 41, 41, 9, 9, 11, 13, 9, 41]
theorem block26 : ∀ u ∈ List.range 32, !valid5 (832+u) || check (word5 (832+u)) cert26[u]! = true := by decide +kernel
def cert27 : Array Nat := #[13, 9, 11, 41, 41, 11, 11, 11, 43, 11, 43, 77, 11, 11, 105, 43, 13, 13, 45, 13, 13, 45, 13, 13, 75, 45, 105, 9, 9, 11, 13, 9]
theorem block27 : ∀ u ∈ List.range 32, !valid5 (864+u) || check (word5 (864+u)) cert27[u]! = true := by decide +kernel
def cert28 : Array Nat := #[41, 13, 9, 11, 41, 41, 73, 73, 75, 77, 73, 105, 77, 73, 75, 105, 105, 13, 13, 45, 13, 13, 45, 13, 13, 6770769, 45, 34512609, 9, 9, 11, 13]
theorem block28 : ∀ u ∈ List.range 32, !valid5 (896+u) || check (word5 (896+u)) cert28[u]! = true := by decide +kernel
def cert29 : Array Nat := #[9, 41, 13, 9, 11, 41, 41, 11, 11, 11, 43, 11, 43, 6738065, 11, 11, 23244513, 43, 73, 73, 105, 77, 73, 105, 77, 73, 23276769, 105, 105, 73, 73, 75]
theorem block29 : ∀ u ∈ List.range 32, !valid5 (928+u) || check (word5 (928+u)) cert29[u]! = true := by decide +kernel
def cert30 : Array Nat := #[105, 73, 105, 34544865, 73, 75, 105, 105, 10, 11, 10, 42, 10, 26, 42, 11, 10, 26, 42, 11, 11, 11, 43, 11, 43, 106, 11, 11, 90, 43, 10, 11]
theorem block30 : ∀ u ∈ List.range 32, !valid5 (960+u) || check (word5 (960+u)) cert30[u]! = true := by decide +kernel
def cert31 : Array Nat := #[10, 42, 10, 26, 42, 11, 10, 26, 42, 74, 75, 74, 106, 74, 90, 106, 75, 74, 90, 106, 10, 11, 10, 42, 10, 26, 42, 11, 10, 26, 42, 26]
theorem block31 : ∀ u ∈ List.range 32, !valid5 (992+u) || check (word5 (992+u)) cert31[u]! = true := by decide +kernel

theorem portion3 (h : Nat) (lo : 768≤h) (hi : h<1024) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t28 : h<896
  ·
    by_cases t26 : h<832
    ·
      by_cases t25 : h<800
      ·
        have H := block24 (h-768) (List.mem_range.mpr (by omega))
        have E : 768+(h-768)=h := by omega
        rw [E,valid] at H
        exact ⟨cert24[h-768]!,by simpa using H⟩
      ·
        have H := block25 (h-800) (List.mem_range.mpr (by omega))
        have E : 800+(h-800)=h := by omega
        rw [E,valid] at H
        exact ⟨cert25[h-800]!,by simpa using H⟩
    ·
      by_cases t27 : h<864
      ·
        have H := block26 (h-832) (List.mem_range.mpr (by omega))
        have E : 832+(h-832)=h := by omega
        rw [E,valid] at H
        exact ⟨cert26[h-832]!,by simpa using H⟩
      ·
        have H := block27 (h-864) (List.mem_range.mpr (by omega))
        have E : 864+(h-864)=h := by omega
        rw [E,valid] at H
        exact ⟨cert27[h-864]!,by simpa using H⟩
  ·
    by_cases t30 : h<960
    ·
      by_cases t29 : h<928
      ·
        have H := block28 (h-896) (List.mem_range.mpr (by omega))
        have E : 896+(h-896)=h := by omega
        rw [E,valid] at H
        exact ⟨cert28[h-896]!,by simpa using H⟩
      ·
        have H := block29 (h-928) (List.mem_range.mpr (by omega))
        have E : 928+(h-928)=h := by omega
        rw [E,valid] at H
        exact ⟨cert29[h-928]!,by simpa using H⟩
    ·
      by_cases t31 : h<992
      ·
        have H := block30 (h-960) (List.mem_range.mpr (by omega))
        have E : 960+(h-960)=h := by omega
        rw [E,valid] at H
        exact ⟨cert30[h-960]!,by simpa using H⟩
      ·
        have H := block31 (h-992) (List.mem_range.mpr (by omega))
        have E : 992+(h-992)=h := by omega
        rw [E,valid] at H
        exact ⟨cert31[h-992]!,by simpa using H⟩
end BikovEight
