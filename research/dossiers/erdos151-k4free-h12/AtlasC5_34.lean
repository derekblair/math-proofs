import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert272 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 101, 0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101, 0]
theorem block272 : ∀ u ∈ List.range 32, !valid5 (8704+u) || check (word5 (8704+u)) cert272[u]! = true := by decide +kernel
def cert273 : Array Nat := #[101, 0, 101, 101, 0, 0, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101, 0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 101]
theorem block273 : ∀ u ∈ List.range 32, !valid5 (8736+u) || check (word5 (8736+u)) cert273[u]! = true := by decide +kernel
def cert274 : Array Nat := #[0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block274 : ∀ u ∈ List.range 32, !valid5 (8768+u) || check (word5 (8768+u)) cert274[u]! = true := by decide +kernel
def cert275 : Array Nat := #[101, 0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 101, 0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block275 : ∀ u ∈ List.range 32, !valid5 (8800+u) || check (word5 (8800+u)) cert275[u]! = true := by decide +kernel
def cert276 : Array Nat := #[0, 105, 0, 105, 105, 0, 105, 0, 0, 0, 105, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 0, 105, 105, 0, 105, 0, 0, 0]
theorem block276 : ∀ u ∈ List.range 32, !valid5 (8832+u) || check (word5 (8832+u)) cert276[u]! = true := by decide +kernel
def cert277 : Array Nat := #[105, 105, 105, 0, 105, 105, 0, 105, 0, 0, 0, 105, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 0, 105, 105, 0, 105, 0, 0]
theorem block277 : ∀ u ∈ List.range 32, !valid5 (8864+u) || check (word5 (8864+u)) cert277[u]! = true := by decide +kernel
def cert278 : Array Nat := #[0, 105, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block278 : ∀ u ∈ List.range 32, !valid5 (8896+u) || check (word5 (8896+u)) cert278[u]! = true := by decide +kernel
def cert279 : Array Nat := #[0, 0, 0, 0, 105, 0, 105, 105, 0, 105, 0, 0, 0, 105, 105, 105, 0, 105, 105, 0, 105, 0, 0, 0, 105, 105, 106, 106, 0, 106, 0, 106]
theorem block279 : ∀ u ∈ List.range 32, !valid5 (8928+u) || check (word5 (8928+u)) cert279[u]! = true := by decide +kernel

theorem portion34 (h : Nat) (lo : 8704≤h) (hi : h<8960) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t276 : h<8832
  ·
    by_cases t274 : h<8768
    ·
      by_cases t273 : h<8736
      ·
        have H := block272 (h-8704) (List.mem_range.mpr (by omega))
        have E : 8704+(h-8704)=h := by omega
        rw [E,valid] at H
        exact ⟨cert272[h-8704]!,by simpa using H⟩
      ·
        have H := block273 (h-8736) (List.mem_range.mpr (by omega))
        have E : 8736+(h-8736)=h := by omega
        rw [E,valid] at H
        exact ⟨cert273[h-8736]!,by simpa using H⟩
    ·
      by_cases t275 : h<8800
      ·
        have H := block274 (h-8768) (List.mem_range.mpr (by omega))
        have E : 8768+(h-8768)=h := by omega
        rw [E,valid] at H
        exact ⟨cert274[h-8768]!,by simpa using H⟩
      ·
        have H := block275 (h-8800) (List.mem_range.mpr (by omega))
        have E : 8800+(h-8800)=h := by omega
        rw [E,valid] at H
        exact ⟨cert275[h-8800]!,by simpa using H⟩
  ·
    by_cases t278 : h<8896
    ·
      by_cases t277 : h<8864
      ·
        have H := block276 (h-8832) (List.mem_range.mpr (by omega))
        have E : 8832+(h-8832)=h := by omega
        rw [E,valid] at H
        exact ⟨cert276[h-8832]!,by simpa using H⟩
      ·
        have H := block277 (h-8864) (List.mem_range.mpr (by omega))
        have E : 8864+(h-8864)=h := by omega
        rw [E,valid] at H
        exact ⟨cert277[h-8864]!,by simpa using H⟩
    ·
      by_cases t279 : h<8928
      ·
        have H := block278 (h-8896) (List.mem_range.mpr (by omega))
        have E : 8896+(h-8896)=h := by omega
        rw [E,valid] at H
        exact ⟨cert278[h-8896]!,by simpa using H⟩
      ·
        have H := block279 (h-8928) (List.mem_range.mpr (by omega))
        have E : 8928+(h-8928)=h := by omega
        rw [E,valid] at H
        exact ⟨cert279[h-8928]!,by simpa using H⟩
end BikovEight
