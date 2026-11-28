import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert304 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block304 : ∀ u ∈ List.range 32, !valid5 (9728+u) || check (word5 (9728+u)) cert304[u]! = true := by decide +kernel
def cert305 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block305 : ∀ u ∈ List.range 32, !valid5 (9760+u) || check (word5 (9760+u)) cert305[u]! = true := by decide +kernel
def cert306 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block306 : ∀ u ∈ List.range 32, !valid5 (9792+u) || check (word5 (9792+u)) cert306[u]! = true := by decide +kernel
def cert307 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block307 : ∀ u ∈ List.range 32, !valid5 (9824+u) || check (word5 (9824+u)) cert307[u]! = true := by decide +kernel
def cert308 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block308 : ∀ u ∈ List.range 32, !valid5 (9856+u) || check (word5 (9856+u)) cert308[u]! = true := by decide +kernel
def cert309 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block309 : ∀ u ∈ List.range 32, !valid5 (9888+u) || check (word5 (9888+u)) cert309[u]! = true := by decide +kernel
def cert310 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block310 : ∀ u ∈ List.range 32, !valid5 (9920+u) || check (word5 (9920+u)) cert310[u]! = true := by decide +kernel
def cert311 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block311 : ∀ u ∈ List.range 32, !valid5 (9952+u) || check (word5 (9952+u)) cert311[u]! = true := by decide +kernel

theorem portion38 (h : Nat) (lo : 9728≤h) (hi : h<9984) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t308 : h<9856
  ·
    by_cases t306 : h<9792
    ·
      by_cases t305 : h<9760
      ·
        have H := block304 (h-9728) (List.mem_range.mpr (by omega))
        have E : 9728+(h-9728)=h := by omega
        rw [E,valid] at H
        exact ⟨cert304[h-9728]!,by simpa using H⟩
      ·
        have H := block305 (h-9760) (List.mem_range.mpr (by omega))
        have E : 9760+(h-9760)=h := by omega
        rw [E,valid] at H
        exact ⟨cert305[h-9760]!,by simpa using H⟩
    ·
      by_cases t307 : h<9824
      ·
        have H := block306 (h-9792) (List.mem_range.mpr (by omega))
        have E : 9792+(h-9792)=h := by omega
        rw [E,valid] at H
        exact ⟨cert306[h-9792]!,by simpa using H⟩
      ·
        have H := block307 (h-9824) (List.mem_range.mpr (by omega))
        have E : 9824+(h-9824)=h := by omega
        rw [E,valid] at H
        exact ⟨cert307[h-9824]!,by simpa using H⟩
  ·
    by_cases t310 : h<9920
    ·
      by_cases t309 : h<9888
      ·
        have H := block308 (h-9856) (List.mem_range.mpr (by omega))
        have E : 9856+(h-9856)=h := by omega
        rw [E,valid] at H
        exact ⟨cert308[h-9856]!,by simpa using H⟩
      ·
        have H := block309 (h-9888) (List.mem_range.mpr (by omega))
        have E : 9888+(h-9888)=h := by omega
        rw [E,valid] at H
        exact ⟨cert309[h-9888]!,by simpa using H⟩
    ·
      by_cases t311 : h<9952
      ·
        have H := block310 (h-9920) (List.mem_range.mpr (by omega))
        have E : 9920+(h-9920)=h := by omega
        rw [E,valid] at H
        exact ⟨cert310[h-9920]!,by simpa using H⟩
      ·
        have H := block311 (h-9952) (List.mem_range.mpr (by omega))
        have E : 9952+(h-9952)=h := by omega
        rw [E,valid] at H
        exact ⟨cert311[h-9952]!,by simpa using H⟩
end BikovEight
