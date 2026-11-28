import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert168 : Array Nat := #[101, 82, 84, 69, 69, 74, 69, 73, 101, 69, 73, 74, 101, 105, 74, 106, 74, 106, 74, 82, 106, 114, 74, 82, 106, 82, 114, 82, 84, 114, 82, 114]
theorem block168 : ∀ u ∈ List.range 32, !valid5 (5376+u) || check (word5 (5376+u)) cert168[u]! = true := by decide +kernel
def cert169 : Array Nat := #[114, 116, 82, 84, 69, 69, 101, 69, 101, 84, 69, 116, 101, 101, 84, 69, 69, 101, 69, 73, 101, 69, 73, 101, 101, 105, 73, 73, 74, 105, 73, 105]
theorem block169 : ∀ u ∈ List.range 32, !valid5 (5408+u) || check (word5 (5408+u)) cert169[u]! = true := by decide +kernel
def cert170 : Array Nat := #[106, 73, 74, 105, 105, 69, 69, 75, 69, 73, 85, 69, 73, 75, 101, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 101, 69, 73]
theorem block170 : ∀ u ∈ List.range 32, !valid5 (5440+u) || check (word5 (5440+u)) cert170[u]! = true := by decide +kernel
def cert171 : Array Nat := #[85, 69, 73, 101, 101, 85, 73, 73, 75, 105, 73, 105, 34544696, 73, 75, 105, 105, 69, 69, 101, 69, 101, 85, 69, 51071864, 101, 101, 85, 69, 69, 75, 69]
theorem block171 : ∀ u ∈ List.range 32, !valid5 (5472+u) || check (word5 (5472+u)) cert171[u]! = true := by decide +kernel
def cert172 : Array Nat := #[73, 101, 69, 73, 75, 101, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 101]
theorem block172 : ∀ u ∈ List.range 32, !valid5 (5504+u) || check (word5 (5504+u)) cert172[u]! = true := by decide +kernel
def cert173 : Array Nat := #[69, 101, 85, 69, 6802353, 101, 101, 85, 69, 69, 101, 69, 73, 101, 69, 73, 101, 101, 105, 73, 73, 75, 105, 73, 105, 5479409, 73, 75, 105, 105, 74, 75]
theorem block173 : ∀ u ∈ List.range 32, !valid5 (5536+u) || check (word5 (5536+u)) cert173[u]! = true := by decide +kernel
def cert174 : Array Nat := #[74, 86, 74, 82, 106, 75, 74, 82, 86, 74, 106, 74, 86, 74, 82, 106, 114, 74, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74]
theorem block174 : ∀ u ∈ List.range 32, !valid5 (5568+u) || check (word5 (5568+u)) cert174[u]! = true := by decide +kernel
def cert175 : Array Nat := #[75, 74, 106, 74, 82, 106, 75, 74, 82, 106, 82, 114, 82, 86, 114, 82, 114, 114, 53685048, 82, 86, 74, 75, 74, 106, 74, 106, 106, 75, 74, 70192056, 106]
theorem block175 : ∀ u ∈ List.range 32, !valid5 (5600+u) || check (word5 (5600+u)) cert175[u]! = true := by decide +kernel

theorem portion21 (h : Nat) (lo : 5376≤h) (hi : h<5632) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t172 : h<5504
  ·
    by_cases t170 : h<5440
    ·
      by_cases t169 : h<5408
      ·
        have H := block168 (h-5376) (List.mem_range.mpr (by omega))
        have E : 5376+(h-5376)=h := by omega
        rw [E,valid] at H
        exact ⟨cert168[h-5376]!,by simpa using H⟩
      ·
        have H := block169 (h-5408) (List.mem_range.mpr (by omega))
        have E : 5408+(h-5408)=h := by omega
        rw [E,valid] at H
        exact ⟨cert169[h-5408]!,by simpa using H⟩
    ·
      by_cases t171 : h<5472
      ·
        have H := block170 (h-5440) (List.mem_range.mpr (by omega))
        have E : 5440+(h-5440)=h := by omega
        rw [E,valid] at H
        exact ⟨cert170[h-5440]!,by simpa using H⟩
      ·
        have H := block171 (h-5472) (List.mem_range.mpr (by omega))
        have E : 5472+(h-5472)=h := by omega
        rw [E,valid] at H
        exact ⟨cert171[h-5472]!,by simpa using H⟩
  ·
    by_cases t174 : h<5568
    ·
      by_cases t173 : h<5536
      ·
        have H := block172 (h-5504) (List.mem_range.mpr (by omega))
        have E : 5504+(h-5504)=h := by omega
        rw [E,valid] at H
        exact ⟨cert172[h-5504]!,by simpa using H⟩
      ·
        have H := block173 (h-5536) (List.mem_range.mpr (by omega))
        have E : 5536+(h-5536)=h := by omega
        rw [E,valid] at H
        exact ⟨cert173[h-5536]!,by simpa using H⟩
    ·
      by_cases t175 : h<5600
      ·
        have H := block174 (h-5568) (List.mem_range.mpr (by omega))
        have E : 5568+(h-5568)=h := by omega
        rw [E,valid] at H
        exact ⟨cert174[h-5568]!,by simpa using H⟩
      ·
        have H := block175 (h-5600) (List.mem_range.mpr (by omega))
        have E : 5600+(h-5600)=h := by omega
        rw [E,valid] at H
        exact ⟨cert175[h-5600]!,by simpa using H⟩
end BikovEight
