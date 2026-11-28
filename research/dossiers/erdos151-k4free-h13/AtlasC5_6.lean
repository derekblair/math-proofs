import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert48 : Array Nat := #[0, 0, 41, 41, 43, 69, 0, 43, 0, 43, 69, 0, 0, 0, 43, 69, 69, 0, 69, 73, 0, 69, 73, 0, 0, 0, 53, 73, 53, 0, 53, 0]
theorem block48 : ∀ u ∈ List.range 32, !valid5 (1536+u) || check (word5 (1536+u)) cert48[u]! = true := by decide +kernel
def cert49 : Array Nat := #[0, 73, 53, 0, 0, 42, 42, 74, 42, 50, 42, 42, 50, 74, 82, 42, 43, 0, 74, 43, 74, 43, 0, 0, 74, 82, 43, 42, 42, 0, 42, 50]
theorem block49 : ∀ u ∈ List.range 32, !valid5 (1568+u) || check (word5 (1568+u)) cert49[u]! = true := by decide +kernel
def cert50 : Array Nat := #[42, 42, 50, 0, 0, 42, 54, 54, 74, 0, 54, 82, 0, 54, 74, 82, 0, 42, 42, 82, 42, 0, 42, 42, 0, 0, 82, 42, 50, 50, 74, 50]
theorem block50 : ∀ u ∈ List.range 32, !valid5 (1600+u) || check (word5 (1600+u)) cert50[u]! = true := by decide +kernel
def cert51 : Array Nat := #[50, 0, 50, 50, 74, 0, 0, 74, 0, 74, 0, 74, 82, 0, 0, 74, 82, 0, 43, 0, 82, 43, 0, 43, 0, 0, 0, 82, 43, 42, 42, 0]
theorem block51 : ∀ u ∈ List.range 32, !valid5 (1632+u) || check (word5 (1632+u)) cert51[u]! = true := by decide +kernel
def cert52 : Array Nat := #[42, 0, 42, 42, 0, 0, 0, 42, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 54, 54, 74, 0, 54, 0, 0, 54, 74, 0, 0, 37, 52]
theorem block52 : ∀ u ∈ List.range 32, !valid5 (1664+u) || check (word5 (1664+u)) cert52[u]! = true := by decide +kernel
def cert53 : Array Nat := #[37, 69, 37, 37, 69, 52, 37, 37, 84, 37, 0, 37, 84, 37, 37, 0, 0, 37, 37, 84, 54, 54, 0, 69, 54, 84, 69, 54, 0, 0, 84, 37]
theorem block53 : ∀ u ∈ List.range 32, !valid5 (1696+u) || check (word5 (1696+u)) cert53[u]! = true := by decide +kernel
def cert54 : Array Nat := #[52, 37, 0, 37, 37, 0, 52, 37, 37, 0, 45, 69, 45, 69, 0, 45, 69, 0, 0, 45, 84, 52, 52, 52, 69, 52, 0, 69, 52, 52, 0, 0]
theorem block54 : ∀ u ∈ List.range 32, !valid5 (1728+u) || check (word5 (1728+u)) cert54[u]! = true := by decide +kernel
def cert55 : Array Nat := #[37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 45, 0, 45, 84, 0, 45, 0, 0, 0, 45, 84, 69, 69, 0, 69, 0, 84, 69, 0, 0, 0]
theorem block55 : ∀ u ∈ List.range 32, !valid5 (1760+u) || check (word5 (1760+u)) cert55[u]! = true := by decide +kernel

theorem portion6 (h : Nat) (lo : 1536≤h) (hi : h<1792) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t52 : h<1664
  ·
    by_cases t50 : h<1600
    ·
      by_cases t49 : h<1568
      ·
        have H := block48 (h-1536) (List.mem_range.mpr (by omega))
        have E : 1536+(h-1536)=h := by omega
        rw [E,valid] at H
        exact ⟨cert48[h-1536]!,by simpa using H⟩
      ·
        have H := block49 (h-1568) (List.mem_range.mpr (by omega))
        have E : 1568+(h-1568)=h := by omega
        rw [E,valid] at H
        exact ⟨cert49[h-1568]!,by simpa using H⟩
    ·
      by_cases t51 : h<1632
      ·
        have H := block50 (h-1600) (List.mem_range.mpr (by omega))
        have E : 1600+(h-1600)=h := by omega
        rw [E,valid] at H
        exact ⟨cert50[h-1600]!,by simpa using H⟩
      ·
        have H := block51 (h-1632) (List.mem_range.mpr (by omega))
        have E : 1632+(h-1632)=h := by omega
        rw [E,valid] at H
        exact ⟨cert51[h-1632]!,by simpa using H⟩
  ·
    by_cases t54 : h<1728
    ·
      by_cases t53 : h<1696
      ·
        have H := block52 (h-1664) (List.mem_range.mpr (by omega))
        have E : 1664+(h-1664)=h := by omega
        rw [E,valid] at H
        exact ⟨cert52[h-1664]!,by simpa using H⟩
      ·
        have H := block53 (h-1696) (List.mem_range.mpr (by omega))
        have E : 1696+(h-1696)=h := by omega
        rw [E,valid] at H
        exact ⟨cert53[h-1696]!,by simpa using H⟩
    ·
      by_cases t55 : h<1760
      ·
        have H := block54 (h-1728) (List.mem_range.mpr (by omega))
        have E : 1728+(h-1728)=h := by omega
        rw [E,valid] at H
        exact ⟨cert54[h-1728]!,by simpa using H⟩
      ·
        have H := block55 (h-1760) (List.mem_range.mpr (by omega))
        have E : 1760+(h-1760)=h := by omega
        rw [E,valid] at H
        exact ⟨cert55[h-1760]!,by simpa using H⟩
end BikovEight
