import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert152 : Array Nat := #[0, 43, 0, 43, 0, 0, 0, 0, 43, 45, 0, 45, 0, 0, 45, 0, 0, 0, 45, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 7655348]
theorem block152 : ∀ u ∈ List.range 32, !valid5 (4864+u) || check (word5 (4864+u)) cert152[u]! = true := by decide +kernel
def cert153 : Array Nat := #[0, 27091437, 43837229, 0, 0, 0, 0, 0, 0, 0, 45, 0, 45, 0, 0, 45, 0, 0, 0, 45, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41]
theorem block153 : ∀ u ∈ List.range 32, !valid5 (4896+u) || check (word5 (4896+u)) cert153[u]! = true := by decide +kernel
def cert154 : Array Nat := #[43, 0, 0, 43, 0, 43, 0, 0, 0, 0, 43, 63003005, 0, 0, 46257214, 0, 0, 0, 0, 0, 0, 0, 13425085, 0, 30168638, 0, 0, 0, 0, 0, 0, 0]
theorem block154 : ∀ u ∈ List.range 32, !valid5 (4928+u) || check (word5 (4928+u)) cert154[u]! = true := by decide +kernel
def cert155 : Array Nat := #[0, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 43, 0, 0, 43, 0, 43, 0, 0, 0, 0, 43, 42, 42, 0, 42, 0, 42, 42, 0, 0]
theorem block155 : ∀ u ∈ List.range 32, !valid5 (4960+u) || check (word5 (4960+u)) cert155[u]! = true := by decide +kernel
def cert156 : Array Nat := #[0, 42, 24391732, 6185965, 0, 0, 0, 73164653, 0, 0, 0, 0, 0, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 58, 58, 0, 58, 0, 0, 58, 0]
theorem block156 : ∀ u ∈ List.range 32, !valid5 (4992+u) || check (word5 (4992+u)) cert156[u]! = true := by decide +kernel
def cert157 : Array Nat := #[0, 0, 0, 63329597, 0, 0, 0, 0, 34971198, 0, 0, 0, 0, 0, 43, 0, 0, 43, 0, 43, 0, 0, 0, 0, 43, 42, 42, 0, 42, 0, 42, 42]
theorem block157 : ∀ u ∈ List.range 32, !valid5 (5024+u) || check (word5 (5024+u)) cert157[u]! = true := by decide +kernel
def cert158 : Array Nat := #[0, 0, 0, 42, 58, 58, 0, 58, 0, 0, 58, 0, 0, 0, 0, 30168637, 13425086, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 0, 50, 50, 0]
theorem block158 : ∀ u ∈ List.range 32, !valid5 (5056+u) || check (word5 (5056+u)) cert158[u]! = true := by decide +kernel
def cert159 : Array Nat := #[50, 50, 0, 0, 0, 26546164, 0, 0, 35513389, 52259181, 0, 0, 0, 0, 0, 0, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 54, 54, 0, 0, 54]
theorem block159 : ∀ u ∈ List.range 32, !valid5 (5088+u) || check (word5 (5088+u)) cert159[u]! = true := by decide +kernel

theorem portion19 (h : Nat) (lo : 4864≤h) (hi : h<5120) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t156 : h<4992
  ·
    by_cases t154 : h<4928
    ·
      by_cases t153 : h<4896
      ·
        have H := block152 (h-4864) (List.mem_range.mpr (by omega))
        have E : 4864+(h-4864)=h := by omega
        rw [E,valid] at H
        exact ⟨cert152[h-4864]!,by simpa using H⟩
      ·
        have H := block153 (h-4896) (List.mem_range.mpr (by omega))
        have E : 4896+(h-4896)=h := by omega
        rw [E,valid] at H
        exact ⟨cert153[h-4896]!,by simpa using H⟩
    ·
      by_cases t155 : h<4960
      ·
        have H := block154 (h-4928) (List.mem_range.mpr (by omega))
        have E : 4928+(h-4928)=h := by omega
        rw [E,valid] at H
        exact ⟨cert154[h-4928]!,by simpa using H⟩
      ·
        have H := block155 (h-4960) (List.mem_range.mpr (by omega))
        have E : 4960+(h-4960)=h := by omega
        rw [E,valid] at H
        exact ⟨cert155[h-4960]!,by simpa using H⟩
  ·
    by_cases t158 : h<5056
    ·
      by_cases t157 : h<5024
      ·
        have H := block156 (h-4992) (List.mem_range.mpr (by omega))
        have E : 4992+(h-4992)=h := by omega
        rw [E,valid] at H
        exact ⟨cert156[h-4992]!,by simpa using H⟩
      ·
        have H := block157 (h-5024) (List.mem_range.mpr (by omega))
        have E : 5024+(h-5024)=h := by omega
        rw [E,valid] at H
        exact ⟨cert157[h-5024]!,by simpa using H⟩
    ·
      by_cases t159 : h<5088
      ·
        have H := block158 (h-5056) (List.mem_range.mpr (by omega))
        have E : 5056+(h-5056)=h := by omega
        rw [E,valid] at H
        exact ⟨cert158[h-5056]!,by simpa using H⟩
      ·
        have H := block159 (h-5088) (List.mem_range.mpr (by omega))
        have E : 5088+(h-5088)=h := by omega
        rw [E,valid] at H
        exact ⟨cert159[h-5088]!,by simpa using H⟩
end BikovEight
