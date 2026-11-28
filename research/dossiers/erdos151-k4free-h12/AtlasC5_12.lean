import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert96 : Array Nat := #[0, 101, 45, 0, 116, 101, 45, 0, 52, 52, 52, 0, 52, 101, 0, 52, 52, 101, 0, 37, 5414392, 37, 0, 37, 37, 0, 34577961, 37, 37, 0, 45, 116]
theorem block96 : ∀ u ∈ List.range 32, !valid5 (3072+u) || check (word5 (3072+u)) cert96[u]! = true := by decide +kernel
def cert97 : Array Nat := #[45, 0, 116, 45, 0, 116, 116, 45, 0, 101, 116, 101, 0, 101, 101, 0, 116, 101, 101, 0, 54, 54, 101, 0, 54, 101, 0, 54, 101, 101, 0, 52]
theorem block97 : ∀ u ∈ List.range 32, !valid5 (3104+u) || check (word5 (3104+u)) cert97[u]! = true := by decide +kernel
def cert98 : Array Nat := #[52, 52, 0, 52, 71482744, 0, 52, 52, 42450217, 0, 41, 42, 41, 41, 0, 41, 42, 0, 0, 41, 41, 41, 106, 41, 41, 0, 41, 106, 0, 0, 41, 41]
theorem block98 : ∀ u ∈ List.range 32, !valid5 (3136+u) || check (word5 (3136+u)) cert98[u]! = true := by decide +kernel
def cert99 : Array Nat := #[42, 42, 105, 42, 0, 42, 42, 0, 0, 105, 42, 45, 106, 45, 105, 0, 45, 106, 0, 0, 45, 105, 41, 42, 41, 41, 0, 41, 42, 0, 0, 41]
theorem block99 : ∀ u ∈ List.range 32, !valid5 (3168+u) || check (word5 (3168+u)) cert99[u]! = true := by decide +kernel
def cert100 : Array Nat := #[41, 58, 58, 105, 58, 0, 105, 58, 0, 0, 105, 105, 45, 106, 45, 106, 0, 45, 106, 0, 0, 45, 106, 41, 6737336, 41, 41, 0, 41, 51105129, 0, 0]
theorem block100 : ∀ u ∈ List.range 32, !valid5 (3200+u) || check (word5 (3200+u)) cert100[u]! = true := by decide +kernel
def cert101 : Array Nat := #[41, 41, 42, 42, 23244344, 42, 0, 42, 42, 0, 0, 53718313, 42, 58, 58, 105, 58, 0, 105, 58, 0, 0, 105, 105, 105, 106, 105, 105, 0, 105, 106, 0]
theorem block101 : ∀ u ∈ List.range 32, !valid5 (3232+u) || check (word5 (3232+u)) cert101[u]! = true := by decide +kernel
def cert102 : Array Nat := #[0, 105, 105, 50, 50, 52, 50, 50, 0, 50, 50, 52, 0, 0, 53, 114, 53, 114, 53, 0, 114, 114, 53, 0, 0, 50, 50, 116, 50, 50, 0, 50]
theorem block102 : ∀ u ∈ List.range 32, !valid5 (3264+u) || check (word5 (3264+u)) cert102[u]! = true := by decide +kernel
def cert103 : Array Nat := #[50, 116, 0, 0, 52, 52, 52, 114, 52, 0, 114, 52, 52, 0, 0, 58, 58, 116, 58, 114, 0, 58, 114, 116, 0, 0, 50, 50, 52, 50, 50, 0]
theorem block103 : ∀ u ∈ List.range 32, !valid5 (3296+u) || check (word5 (3296+u)) cert103[u]! = true := by decide +kernel

theorem portion12 (h : Nat) (lo : 3072≤h) (hi : h<3328) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t100 : h<3200
  ·
    by_cases t98 : h<3136
    ·
      by_cases t97 : h<3104
      ·
        have H := block96 (h-3072) (List.mem_range.mpr (by omega))
        have E : 3072+(h-3072)=h := by omega
        rw [E,valid] at H
        exact ⟨cert96[h-3072]!,by simpa using H⟩
      ·
        have H := block97 (h-3104) (List.mem_range.mpr (by omega))
        have E : 3104+(h-3104)=h := by omega
        rw [E,valid] at H
        exact ⟨cert97[h-3104]!,by simpa using H⟩
    ·
      by_cases t99 : h<3168
      ·
        have H := block98 (h-3136) (List.mem_range.mpr (by omega))
        have E : 3136+(h-3136)=h := by omega
        rw [E,valid] at H
        exact ⟨cert98[h-3136]!,by simpa using H⟩
      ·
        have H := block99 (h-3168) (List.mem_range.mpr (by omega))
        have E : 3168+(h-3168)=h := by omega
        rw [E,valid] at H
        exact ⟨cert99[h-3168]!,by simpa using H⟩
  ·
    by_cases t102 : h<3264
    ·
      by_cases t101 : h<3232
      ·
        have H := block100 (h-3200) (List.mem_range.mpr (by omega))
        have E : 3200+(h-3200)=h := by omega
        rw [E,valid] at H
        exact ⟨cert100[h-3200]!,by simpa using H⟩
      ·
        have H := block101 (h-3232) (List.mem_range.mpr (by omega))
        have E : 3232+(h-3232)=h := by omega
        rw [E,valid] at H
        exact ⟨cert101[h-3232]!,by simpa using H⟩
    ·
      by_cases t103 : h<3296
      ·
        have H := block102 (h-3264) (List.mem_range.mpr (by omega))
        have E : 3264+(h-3264)=h := by omega
        rw [E,valid] at H
        exact ⟨cert102[h-3264]!,by simpa using H⟩
      ·
        have H := block103 (h-3296) (List.mem_range.mpr (by omega))
        have E : 3296+(h-3296)=h := by omega
        rw [E,valid] at H
        exact ⟨cert103[h-3296]!,by simpa using H⟩
end BikovEight
