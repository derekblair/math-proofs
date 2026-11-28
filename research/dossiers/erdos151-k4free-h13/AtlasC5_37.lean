import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert296 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block296 : ∀ u ∈ List.range 32, !valid5 (9472+u) || check (word5 (9472+u)) cert296[u]! = true := by decide +kernel
def cert297 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block297 : ∀ u ∈ List.range 32, !valid5 (9504+u) || check (word5 (9504+u)) cert297[u]! = true := by decide +kernel
def cert298 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block298 : ∀ u ∈ List.range 32, !valid5 (9536+u) || check (word5 (9536+u)) cert298[u]! = true := by decide +kernel
def cert299 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block299 : ∀ u ∈ List.range 32, !valid5 (9568+u) || check (word5 (9568+u)) cert299[u]! = true := by decide +kernel
def cert300 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block300 : ∀ u ∈ List.range 32, !valid5 (9600+u) || check (word5 (9600+u)) cert300[u]! = true := by decide +kernel
def cert301 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block301 : ∀ u ∈ List.range 32, !valid5 (9632+u) || check (word5 (9632+u)) cert301[u]! = true := by decide +kernel
def cert302 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block302 : ∀ u ∈ List.range 32, !valid5 (9664+u) || check (word5 (9664+u)) cert302[u]! = true := by decide +kernel
def cert303 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block303 : ∀ u ∈ List.range 32, !valid5 (9696+u) || check (word5 (9696+u)) cert303[u]! = true := by decide +kernel

theorem portion37 (h : Nat) (lo : 9472≤h) (hi : h<9728) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t300 : h<9600
  ·
    by_cases t298 : h<9536
    ·
      by_cases t297 : h<9504
      ·
        have H := block296 (h-9472) (List.mem_range.mpr (by omega))
        have E : 9472+(h-9472)=h := by omega
        rw [E,valid] at H
        exact ⟨cert296[h-9472]!,by simpa using H⟩
      ·
        have H := block297 (h-9504) (List.mem_range.mpr (by omega))
        have E : 9504+(h-9504)=h := by omega
        rw [E,valid] at H
        exact ⟨cert297[h-9504]!,by simpa using H⟩
    ·
      by_cases t299 : h<9568
      ·
        have H := block298 (h-9536) (List.mem_range.mpr (by omega))
        have E : 9536+(h-9536)=h := by omega
        rw [E,valid] at H
        exact ⟨cert298[h-9536]!,by simpa using H⟩
      ·
        have H := block299 (h-9568) (List.mem_range.mpr (by omega))
        have E : 9568+(h-9568)=h := by omega
        rw [E,valid] at H
        exact ⟨cert299[h-9568]!,by simpa using H⟩
  ·
    by_cases t302 : h<9664
    ·
      by_cases t301 : h<9632
      ·
        have H := block300 (h-9600) (List.mem_range.mpr (by omega))
        have E : 9600+(h-9600)=h := by omega
        rw [E,valid] at H
        exact ⟨cert300[h-9600]!,by simpa using H⟩
      ·
        have H := block301 (h-9632) (List.mem_range.mpr (by omega))
        have E : 9632+(h-9632)=h := by omega
        rw [E,valid] at H
        exact ⟨cert301[h-9632]!,by simpa using H⟩
    ·
      by_cases t303 : h<9696
      ·
        have H := block302 (h-9664) (List.mem_range.mpr (by omega))
        have E : 9664+(h-9664)=h := by omega
        rw [E,valid] at H
        exact ⟨cert302[h-9664]!,by simpa using H⟩
      ·
        have H := block303 (h-9696) (List.mem_range.mpr (by omega))
        have E : 9696+(h-9696)=h := by omega
        rw [E,valid] at H
        exact ⟨cert303[h-9696]!,by simpa using H⟩
end BikovEight
