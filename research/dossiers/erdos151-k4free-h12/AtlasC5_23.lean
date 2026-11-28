import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert184 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 105, 77, 73, 105, 77, 73, 53717809, 105, 105, 73, 73]
theorem block184 : ∀ u ∈ List.range 32, !valid5 (5888+u) || check (word5 (5888+u)) cert184[u]! = true := by decide +kernel
def cert185 : Array Nat := #[74, 105, 73, 105, 106, 73, 74, 105, 105, 82, 85, 82, 84, 90, 82, 85, 114, 90, 82, 84, 82, 114, 82, 84, 90, 82, 114, 114, 90, 82, 84, 84]
theorem block185 : ∀ u ∈ List.range 32, !valid5 (5920+u) || check (word5 (5920+u)) cert185[u]! = true := by decide +kernel
def cert186 : Array Nat := #[85, 116, 84, 116, 84, 85, 116, 116, 25889784, 84, 82, 114, 82, 114, 90, 82, 114, 114, 90, 82, 42416952, 82, 85, 82, 84, 114, 82, 85, 114, 116, 82, 84]
theorem block186 : ∀ u ∈ List.range 32, !valid5 (5952+u) || check (word5 (5952+u)) cert186[u]! = true := by decide +kernel
def cert187 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 114, 82, 114, 90, 82, 114, 114, 90, 82, 71547761, 82, 114, 82, 84, 114, 82, 114, 114, 116, 82]
theorem block187 : ∀ u ∈ List.range 32, !valid5 (5984+u) || check (word5 (5984+u)) cert187[u]! = true := by decide +kernel
def cert188 : Array Nat := #[84, 84, 85, 116, 84, 116, 84, 85, 116, 116, 70224817, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block188 : ∀ u ∈ List.range 32, !valid5 (6016+u) || check (word5 (6016+u)) cert188[u]! = true := by decide +kernel
def cert189 : Array Nat := #[0, 0, 69, 69, 101, 69, 77, 85, 69, 77, 101, 101, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 101, 69, 77, 85, 69, 77]
theorem block189 : ∀ u ∈ List.range 32, !valid5 (6048+u) || check (word5 (6048+u)) cert189[u]! = true := by decide +kernel
def cert190 : Array Nat := #[101, 101, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 101, 69, 101, 85, 69, 51071865, 101, 101, 85, 69, 69, 101, 69, 77, 101, 69]
theorem block190 : ∀ u ∈ List.range 32, !valid5 (6080+u) || check (word5 (6080+u)) cert190[u]! = true := by decide +kernel
def cert191 : Array Nat := #[77, 101, 101, 71515001, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 101, 69, 101, 85]
theorem block191 : ∀ u ∈ List.range 32, !valid5 (6112+u) || check (word5 (6112+u)) cert191[u]! = true := by decide +kernel

theorem portion23 (h : Nat) (lo : 5888≤h) (hi : h<6144) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t188 : h<6016
  ·
    by_cases t186 : h<5952
    ·
      by_cases t185 : h<5920
      ·
        have H := block184 (h-5888) (List.mem_range.mpr (by omega))
        have E : 5888+(h-5888)=h := by omega
        rw [E,valid] at H
        exact ⟨cert184[h-5888]!,by simpa using H⟩
      ·
        have H := block185 (h-5920) (List.mem_range.mpr (by omega))
        have E : 5920+(h-5920)=h := by omega
        rw [E,valid] at H
        exact ⟨cert185[h-5920]!,by simpa using H⟩
    ·
      by_cases t187 : h<5984
      ·
        have H := block186 (h-5952) (List.mem_range.mpr (by omega))
        have E : 5952+(h-5952)=h := by omega
        rw [E,valid] at H
        exact ⟨cert186[h-5952]!,by simpa using H⟩
      ·
        have H := block187 (h-5984) (List.mem_range.mpr (by omega))
        have E : 5984+(h-5984)=h := by omega
        rw [E,valid] at H
        exact ⟨cert187[h-5984]!,by simpa using H⟩
  ·
    by_cases t190 : h<6080
    ·
      by_cases t189 : h<6048
      ·
        have H := block188 (h-6016) (List.mem_range.mpr (by omega))
        have E : 6016+(h-6016)=h := by omega
        rw [E,valid] at H
        exact ⟨cert188[h-6016]!,by simpa using H⟩
      ·
        have H := block189 (h-6048) (List.mem_range.mpr (by omega))
        have E : 6048+(h-6048)=h := by omega
        rw [E,valid] at H
        exact ⟨cert189[h-6048]!,by simpa using H⟩
    ·
      by_cases t191 : h<6112
      ·
        have H := block190 (h-6080) (List.mem_range.mpr (by omega))
        have E : 6080+(h-6080)=h := by omega
        rw [E,valid] at H
        exact ⟨cert190[h-6080]!,by simpa using H⟩
      ·
        have H := block191 (h-6112) (List.mem_range.mpr (by omega))
        have E : 6112+(h-6112)=h := by omega
        rw [E,valid] at H
        exact ⟨cert191[h-6112]!,by simpa using H⟩
end BikovEight
