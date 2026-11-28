import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert176 : Array Nat := #[74, 106, 74, 106, 74, 82, 106, 114, 74, 82, 106, 82, 114, 82, 86, 114, 82, 114, 114, 23309361, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block176 : ∀ u ∈ List.range 32, !valid5 (5632+u) || check (word5 (5632+u)) cert176[u]! = true := by decide +kernel
def cert177 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 75, 74, 106, 74, 106, 106, 75, 74, 25922545, 106, 69, 69, 86, 69, 77, 84, 69, 77, 101]
theorem block177 : ∀ u ∈ List.range 32, !valid5 (5664+u) || check (word5 (5664+u)) cert177[u]! = true := by decide +kernel
def cert178 : Array Nat := #[86, 84, 84, 116, 86, 84, 116, 84, 5446648, 116, 116, 86, 84, 69, 69, 101, 69, 77, 84, 69, 77, 101, 101, 84, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block178 : ∀ u ∈ List.range 32, !valid5 (5696+u) || check (word5 (5696+u)) cert178[u]! = true := by decide +kernel
def cert179 : Array Nat := #[0, 0, 0, 69, 69, 86, 69, 101, 84, 69, 116, 101, 86, 84, 69, 69, 101, 69, 77, 101, 69, 77, 101, 101, 71515000, 0, 0, 0, 0, 0, 0, 0]
theorem block179 : ∀ u ∈ List.range 32, !valid5 (5728+u) || check (word5 (5728+u)) cert179[u]! = true := by decide +kernel
def cert180 : Array Nat := #[0, 0, 0, 0, 84, 116, 86, 84, 116, 84, 34577457, 116, 116, 86, 84, 69, 69, 101, 69, 101, 84, 69, 116, 101, 101, 84, 69, 69, 101, 69, 77, 101]
theorem block180 : ∀ u ∈ List.range 32, !valid5 (5760+u) || check (word5 (5760+u)) cert180[u]! = true := by decide +kernel
def cert181 : Array Nat := #[69, 77, 101, 101, 42449713, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 74, 77, 73, 90, 77, 73, 74, 90, 105, 74, 106, 74, 106, 74]
theorem block181 : ∀ u ∈ List.range 32, !valid5 (5792+u) || check (word5 (5792+u)) cert181[u]! = true := by decide +kernel
def cert182 : Array Nat := #[90, 106, 6769592, 74, 90, 106, 73, 73, 105, 77, 73, 105, 77, 73, 23276600, 105, 105, 73, 73, 74, 105, 73, 90, 106, 73, 74, 90, 105, 0, 0, 0, 0]
theorem block182 : ∀ u ∈ List.range 32, !valid5 (5824+u) || check (word5 (5824+u)) cert182[u]! = true := by decide +kernel
def cert183 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 73, 73, 74, 77, 73, 105, 77, 73, 74, 105, 105, 74, 106, 74, 106, 74, 90, 106, 51104625, 74, 90, 106, 0, 0, 0]
theorem block183 : ∀ u ∈ List.range 32, !valid5 (5856+u) || check (word5 (5856+u)) cert183[u]! = true := by decide +kernel

theorem portion22 (h : Nat) (lo : 5632≤h) (hi : h<5888) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t180 : h<5760
  ·
    by_cases t178 : h<5696
    ·
      by_cases t177 : h<5664
      ·
        have H := block176 (h-5632) (List.mem_range.mpr (by omega))
        have E : 5632+(h-5632)=h := by omega
        rw [E,valid] at H
        exact ⟨cert176[h-5632]!,by simpa using H⟩
      ·
        have H := block177 (h-5664) (List.mem_range.mpr (by omega))
        have E : 5664+(h-5664)=h := by omega
        rw [E,valid] at H
        exact ⟨cert177[h-5664]!,by simpa using H⟩
    ·
      by_cases t179 : h<5728
      ·
        have H := block178 (h-5696) (List.mem_range.mpr (by omega))
        have E : 5696+(h-5696)=h := by omega
        rw [E,valid] at H
        exact ⟨cert178[h-5696]!,by simpa using H⟩
      ·
        have H := block179 (h-5728) (List.mem_range.mpr (by omega))
        have E : 5728+(h-5728)=h := by omega
        rw [E,valid] at H
        exact ⟨cert179[h-5728]!,by simpa using H⟩
  ·
    by_cases t182 : h<5824
    ·
      by_cases t181 : h<5792
      ·
        have H := block180 (h-5760) (List.mem_range.mpr (by omega))
        have E : 5760+(h-5760)=h := by omega
        rw [E,valid] at H
        exact ⟨cert180[h-5760]!,by simpa using H⟩
      ·
        have H := block181 (h-5792) (List.mem_range.mpr (by omega))
        have E : 5792+(h-5792)=h := by omega
        rw [E,valid] at H
        exact ⟨cert181[h-5792]!,by simpa using H⟩
    ·
      by_cases t183 : h<5856
      ·
        have H := block182 (h-5824) (List.mem_range.mpr (by omega))
        have E : 5824+(h-5824)=h := by omega
        rw [E,valid] at H
        exact ⟨cert182[h-5824]!,by simpa using H⟩
      ·
        have H := block183 (h-5856) (List.mem_range.mpr (by omega))
        have E : 5856+(h-5856)=h := by omega
        rw [E,valid] at H
        exact ⟨cert183[h-5856]!,by simpa using H⟩
end BikovEight
