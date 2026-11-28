import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert280 : Array Nat := #[106, 0, 0, 0, 106, 106, 106, 0, 106, 0, 106, 106, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 106, 0, 106, 0]
theorem block280 : ∀ u ∈ List.range 32, !valid5 (8960+u) || check (word5 (8960+u)) cert280[u]! = true := by decide +kernel
def cert281 : Array Nat := #[106, 106, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 106, 0, 106, 0, 106, 106, 0, 0, 0, 106, 106, 106, 0, 106]
theorem block281 : ∀ u ∈ List.range 32, !valid5 (8992+u) || check (word5 (8992+u)) cert281[u]! = true := by decide +kernel
def cert282 : Array Nat := #[0, 106, 106, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block282 : ∀ u ∈ List.range 32, !valid5 (9024+u) || check (word5 (9024+u)) cert282[u]! = true := by decide +kernel
def cert283 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 106, 106, 0, 106, 0, 106, 106, 0, 0, 0, 106, 114, 114, 0, 114, 114, 0, 114, 114, 0, 0, 0, 114, 114]
theorem block283 : ∀ u ∈ List.range 32, !valid5 (9056+u) || check (word5 (9056+u)) cert283[u]! = true := by decide +kernel
def cert284 : Array Nat := #[0, 114, 114, 0, 114, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114, 114, 0, 114, 114, 0, 114, 114, 0, 0, 0, 114]
theorem block284 : ∀ u ∈ List.range 32, !valid5 (9088+u) || check (word5 (9088+u)) cert284[u]! = true := by decide +kernel
def cert285 : Array Nat := #[114, 0, 114, 114, 0, 114, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114, 114, 0, 114, 114, 0, 114, 114, 0, 0, 0]
theorem block285 : ∀ u ∈ List.range 32, !valid5 (9120+u) || check (word5 (9120+u)) cert285[u]! = true := by decide +kernel
def cert286 : Array Nat := #[114, 114, 0, 114, 114, 0, 114, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block286 : ∀ u ∈ List.range 32, !valid5 (9152+u) || check (word5 (9152+u)) cert286[u]! = true := by decide +kernel
def cert287 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 116, 116, 0, 116, 0, 0, 116, 116, 0, 0, 116, 116, 116, 0, 116, 0, 0, 116, 116]
theorem block287 : ∀ u ∈ List.range 32, !valid5 (9184+u) || check (word5 (9184+u)) cert287[u]! = true := by decide +kernel

theorem portion35 (h : Nat) (lo : 8960≤h) (hi : h<9216) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t284 : h<9088
  ·
    by_cases t282 : h<9024
    ·
      by_cases t281 : h<8992
      ·
        have H := block280 (h-8960) (List.mem_range.mpr (by omega))
        have E : 8960+(h-8960)=h := by omega
        rw [E,valid] at H
        exact ⟨cert280[h-8960]!,by simpa using H⟩
      ·
        have H := block281 (h-8992) (List.mem_range.mpr (by omega))
        have E : 8992+(h-8992)=h := by omega
        rw [E,valid] at H
        exact ⟨cert281[h-8992]!,by simpa using H⟩
    ·
      by_cases t283 : h<9056
      ·
        have H := block282 (h-9024) (List.mem_range.mpr (by omega))
        have E : 9024+(h-9024)=h := by omega
        rw [E,valid] at H
        exact ⟨cert282[h-9024]!,by simpa using H⟩
      ·
        have H := block283 (h-9056) (List.mem_range.mpr (by omega))
        have E : 9056+(h-9056)=h := by omega
        rw [E,valid] at H
        exact ⟨cert283[h-9056]!,by simpa using H⟩
  ·
    by_cases t286 : h<9152
    ·
      by_cases t285 : h<9120
      ·
        have H := block284 (h-9088) (List.mem_range.mpr (by omega))
        have E : 9088+(h-9088)=h := by omega
        rw [E,valid] at H
        exact ⟨cert284[h-9088]!,by simpa using H⟩
      ·
        have H := block285 (h-9120) (List.mem_range.mpr (by omega))
        have E : 9120+(h-9120)=h := by omega
        rw [E,valid] at H
        exact ⟨cert285[h-9120]!,by simpa using H⟩
    ·
      by_cases t287 : h<9184
      ·
        have H := block286 (h-9152) (List.mem_range.mpr (by omega))
        have E : 9152+(h-9152)=h := by omega
        rw [E,valid] at H
        exact ⟨cert286[h-9152]!,by simpa using H⟩
      ·
        have H := block287 (h-9184) (List.mem_range.mpr (by omega))
        have E : 9184+(h-9184)=h := by omega
        rw [E,valid] at H
        exact ⟨cert287[h-9184]!,by simpa using H⟩
end BikovEight
