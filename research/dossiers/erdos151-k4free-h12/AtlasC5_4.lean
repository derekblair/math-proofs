import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert32 : Array Nat := #[58, 26, 58, 26, 26, 58, 75, 26, 26, 106, 74, 106, 74, 106, 74, 90, 106, 6769873, 74, 90, 106, 11, 11, 11, 43, 11, 43, 6737617, 11, 11, 23244961, 43]
theorem block32 : ∀ u ∈ List.range 32, !valid5 (1024+u) || check (word5 (1024+u)) cert32[u]! = true := by decide +kernel
def cert33 : Array Nat := #[10, 11, 10, 42, 10, 26, 42, 11, 10, 26, 42, 26, 58, 26, 58, 26, 26, 58, 23277665, 26, 26, 25923161, 74, 75, 74, 106, 74, 106, 106, 75, 74, 25922713]
theorem block33 : ∀ u ∈ List.range 32, !valid5 (1056+u) || check (word5 (1056+u)) cert33[u]! = true := by decide +kernel
def cert34 : Array Nat := #[106, 18, 50, 18, 22, 26, 18, 50, 50, 26, 18, 22, 82, 114, 82, 86, 90, 82, 114, 114, 90, 82, 86, 18, 50, 18, 22, 26, 18, 50, 50, 26]
theorem block34 : ∀ u ∈ List.range 32, !valid5 (1088+u) || check (word5 (1088+u)) cert34[u]! = true := by decide +kernel
def cert35 : Array Nat := #[18, 22, 22, 54, 22, 22, 54, 22, 114, 54, 90, 22, 22, 26, 58, 26, 58, 26, 26, 58, 114, 26, 26, 86, 18, 50, 18, 22, 26, 18, 50, 50]
theorem block35 : ∀ u ∈ List.range 32, !valid5 (1120+u) || check (word5 (1120+u)) cert35[u]! = true := by decide +kernel
def cert36 : Array Nat := #[26, 18, 22, 82, 114, 82, 114, 90, 82, 114, 114, 90, 82, 71548041, 82, 114, 82, 86, 114, 82, 114, 114, 23309473, 82, 86, 26, 58, 26, 58, 26, 26, 58]
theorem block36 : ∀ u ∈ List.range 32, !valid5 (1152+u) || check (word5 (1152+u)) cert36[u]! = true := by decide +kernel
def cert37 : Array Nat := #[23309921, 26, 26, 25890905, 18, 50, 18, 22, 26, 18, 50, 50, 26, 18, 22, 22, 54, 22, 22, 54, 22, 71548489, 54, 25858201, 22, 22, 20, 21, 22, 20, 52, 20]
theorem block37 : ∀ u ∈ List.range 32, !valid5 (1184+u) || check (word5 (1184+u)) cert37[u]! = true := by decide +kernel
def cert38 : Array Nat := #[21, 52, 52, 22, 20, 21, 21, 53, 21, 53, 21, 21, 116, 53, 86, 21, 22, 54, 22, 22, 54, 22, 85, 54, 116, 22, 22, 20, 21, 22, 20, 52]
theorem block38 : ∀ u ∈ List.range 32, !valid5 (1216+u) || check (word5 (1216+u)) cert38[u]! = true := by decide +kernel
def cert39 : Array Nat := #[20, 21, 52, 52, 22, 20, 84, 85, 86, 84, 116, 84, 85, 116, 116, 86, 84, 20, 21, 22, 20, 52, 20, 21, 52, 52, 22, 20, 21, 21, 53, 21]
theorem block39 : ∀ u ∈ List.range 32, !valid5 (1248+u) || check (word5 (1248+u)) cert39[u]! = true := by decide +kernel

theorem portion4 (h : Nat) (lo : 1024≤h) (hi : h<1280) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t36 : h<1152
  ·
    by_cases t34 : h<1088
    ·
      by_cases t33 : h<1056
      ·
        have H := block32 (h-1024) (List.mem_range.mpr (by omega))
        have E : 1024+(h-1024)=h := by omega
        rw [E,valid] at H
        exact ⟨cert32[h-1024]!,by simpa using H⟩
      ·
        have H := block33 (h-1056) (List.mem_range.mpr (by omega))
        have E : 1056+(h-1056)=h := by omega
        rw [E,valid] at H
        exact ⟨cert33[h-1056]!,by simpa using H⟩
    ·
      by_cases t35 : h<1120
      ·
        have H := block34 (h-1088) (List.mem_range.mpr (by omega))
        have E : 1088+(h-1088)=h := by omega
        rw [E,valid] at H
        exact ⟨cert34[h-1088]!,by simpa using H⟩
      ·
        have H := block35 (h-1120) (List.mem_range.mpr (by omega))
        have E : 1120+(h-1120)=h := by omega
        rw [E,valid] at H
        exact ⟨cert35[h-1120]!,by simpa using H⟩
  ·
    by_cases t38 : h<1216
    ·
      by_cases t37 : h<1184
      ·
        have H := block36 (h-1152) (List.mem_range.mpr (by omega))
        have E : 1152+(h-1152)=h := by omega
        rw [E,valid] at H
        exact ⟨cert36[h-1152]!,by simpa using H⟩
      ·
        have H := block37 (h-1184) (List.mem_range.mpr (by omega))
        have E : 1184+(h-1184)=h := by omega
        rw [E,valid] at H
        exact ⟨cert37[h-1184]!,by simpa using H⟩
    ·
      by_cases t39 : h<1248
      ·
        have H := block38 (h-1216) (List.mem_range.mpr (by omega))
        have E : 1216+(h-1216)=h := by omega
        rw [E,valid] at H
        exact ⟨cert38[h-1216]!,by simpa using H⟩
      ·
        have H := block39 (h-1248) (List.mem_range.mpr (by omega))
        have E : 1248+(h-1248)=h := by omega
        rw [E,valid] at H
        exact ⟨cert39[h-1248]!,by simpa using H⟩
end BikovEight
