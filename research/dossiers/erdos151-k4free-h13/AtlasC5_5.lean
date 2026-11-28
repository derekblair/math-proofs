import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert40 : Array Nat := #[53, 21, 21, 34578017, 53, 71483529, 21, 84, 116, 86, 84, 116, 84, 34577569, 116, 116, 86, 84, 84, 85, 116, 84, 116, 84, 85, 116, 116, 25890009, 84, 22, 54, 22]
theorem block40 : ∀ u ∈ List.range 32, !valid5 (1280+u) || check (word5 (1280+u)) cert40[u]! = true := by decide +kernel
def cert41 : Array Nat := #[22, 54, 22, 71516233, 54, 25857753, 22, 22, 20, 21, 22, 20, 52, 20, 21, 52, 52, 22, 20, 37, 42, 37, 41, 37, 37, 42, 50, 37, 37, 41, 37, 0]
theorem block41 : ∀ u ∈ List.range 32, !valid5 (1312+u) || check (word5 (1312+u)) cert41[u]! = true := by decide +kernel
def cert42 : Array Nat := #[37, 41, 37, 37, 0, 0, 37, 37, 41, 42, 42, 0, 42, 50, 42, 42, 50, 0, 0, 42, 37, 52, 37, 0, 37, 37, 0, 52, 37, 37, 0, 41]
theorem block42 : ∀ u ∈ List.range 32, !valid5 (1344+u) || check (word5 (1344+u)) cert42[u]! = true := by decide +kernel
def cert43 : Array Nat := #[42, 41, 41, 0, 41, 42, 0, 0, 41, 41, 50, 50, 52, 50, 50, 0, 50, 50, 52, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0]
theorem block43 : ∀ u ∈ List.range 32, !valid5 (1376+u) || check (word5 (1376+u)) cert43[u]! = true := by decide +kernel
def cert44 : Array Nat := #[41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0]
theorem block44 : ∀ u ∈ List.range 32, !valid5 (1408+u) || check (word5 (1408+u)) cert44[u]! = true := by decide +kernel
def cert45 : Array Nat := #[0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 37, 69, 37, 41, 37, 37, 69, 73, 37, 37, 41, 37, 0, 37, 41, 37, 37, 0, 0, 37]
theorem block45 : ∀ u ∈ List.range 32, !valid5 (1440+u) || check (word5 (1440+u)) cert45[u]! = true := by decide +kernel
def cert46 : Array Nat := #[37, 41, 43, 69, 0, 43, 73, 43, 69, 73, 0, 0, 43, 37, 73, 37, 0, 37, 37, 0, 73, 37, 37, 0, 41, 69, 41, 41, 0, 41, 69, 0]
theorem block46 : ∀ u ∈ List.range 32, !valid5 (1472+u) || check (word5 (1472+u)) cert46[u]! = true := by decide +kernel
def cert47 : Array Nat := #[0, 41, 41, 53, 69, 53, 69, 53, 0, 69, 73, 53, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 41, 0, 41, 41, 0, 41, 0]
theorem block47 : ∀ u ∈ List.range 32, !valid5 (1504+u) || check (word5 (1504+u)) cert47[u]! = true := by decide +kernel

theorem portion5 (h : Nat) (lo : 1280≤h) (hi : h<1536) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t44 : h<1408
  ·
    by_cases t42 : h<1344
    ·
      by_cases t41 : h<1312
      ·
        have H := block40 (h-1280) (List.mem_range.mpr (by omega))
        have E : 1280+(h-1280)=h := by omega
        rw [E,valid] at H
        exact ⟨cert40[h-1280]!,by simpa using H⟩
      ·
        have H := block41 (h-1312) (List.mem_range.mpr (by omega))
        have E : 1312+(h-1312)=h := by omega
        rw [E,valid] at H
        exact ⟨cert41[h-1312]!,by simpa using H⟩
    ·
      by_cases t43 : h<1376
      ·
        have H := block42 (h-1344) (List.mem_range.mpr (by omega))
        have E : 1344+(h-1344)=h := by omega
        rw [E,valid] at H
        exact ⟨cert42[h-1344]!,by simpa using H⟩
      ·
        have H := block43 (h-1376) (List.mem_range.mpr (by omega))
        have E : 1376+(h-1376)=h := by omega
        rw [E,valid] at H
        exact ⟨cert43[h-1376]!,by simpa using H⟩
  ·
    by_cases t46 : h<1472
    ·
      by_cases t45 : h<1440
      ·
        have H := block44 (h-1408) (List.mem_range.mpr (by omega))
        have E : 1408+(h-1408)=h := by omega
        rw [E,valid] at H
        exact ⟨cert44[h-1408]!,by simpa using H⟩
      ·
        have H := block45 (h-1440) (List.mem_range.mpr (by omega))
        have E : 1440+(h-1440)=h := by omega
        rw [E,valid] at H
        exact ⟨cert45[h-1440]!,by simpa using H⟩
    ·
      by_cases t47 : h<1504
      ·
        have H := block46 (h-1472) (List.mem_range.mpr (by omega))
        have E : 1472+(h-1472)=h := by omega
        rw [E,valid] at H
        exact ⟨cert46[h-1472]!,by simpa using H⟩
      ·
        have H := block47 (h-1504) (List.mem_range.mpr (by omega))
        have E : 1504+(h-1504)=h := by omega
        rw [E,valid] at H
        exact ⟨cert47[h-1504]!,by simpa using H⟩
end BikovEight
