import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert8 : Array Nat := #[43, 11, 43, 106, 11, 11, 82, 43, 10, 11, 10, 22, 10, 18, 42, 11, 10, 18, 22, 22, 54, 22, 22, 54, 22, 106, 54, 74, 22, 22, 10, 11]
theorem block8 : ∀ u ∈ List.range 32, !valid5 (256+u) || check (word5 (256+u)) cert8[u]! = true := by decide +kernel
def cert9 : Array Nat := #[10, 42, 10, 26, 42, 11, 10, 26, 42, 18, 50, 18, 22, 26, 18, 50, 50, 26, 18, 22, 74, 106, 74, 106, 74, 82, 106, 114, 74, 82, 106, 11]
theorem block9 : ∀ u ∈ List.range 32, !valid5 (288+u) || check (word5 (288+u)) cert9[u]! = true := by decide +kernel
def cert10 : Array Nat := #[11, 11, 43, 11, 43, 114, 11, 11, 82, 43, 10, 11, 10, 42, 10, 26, 42, 11, 10, 26, 42, 18, 50, 18, 22, 26, 18, 50, 50, 26, 18, 22]
theorem block10 : ∀ u ∈ List.range 32, !valid5 (320+u) || check (word5 (320+u)) cert10[u]! = true := by decide +kernel
def cert11 : Array Nat := #[22, 54, 22, 22, 54, 22, 106, 54, 74, 22, 22, 5, 5, 22, 5, 13, 20, 5, 13, 37, 22, 20, 5, 5, 37, 5, 13, 21, 5, 13, 37, 37]
theorem block11 : ∀ u ∈ List.range 32, !valid5 (352+u) || check (word5 (352+u)) cert11[u]! = true := by decide +kernel
def cert12 : Array Nat := #[21, 22, 54, 22, 22, 54, 22, 69, 54, 101, 22, 22, 5, 5, 22, 5, 13, 20, 5, 13, 37, 22, 20, 13, 13, 45, 13, 13, 45, 13, 13, 101]
theorem block12 : ∀ u ∈ List.range 32, !valid5 (384+u) || check (word5 (384+u)) cert12[u]! = true := by decide +kernel
def cert13 : Array Nat := #[45, 84, 20, 21, 22, 20, 52, 20, 21, 52, 52, 22, 20, 5, 5, 37, 5, 13, 21, 5, 13, 37, 37, 21, 13, 13, 45, 13, 13, 45, 13, 13]
theorem block13 : ∀ u ∈ List.range 32, !valid5 (416+u) || check (word5 (416+u)) cert13[u]! = true := by decide +kernel
def cert14 : Array Nat := #[116, 45, 84, 69, 69, 101, 69, 101, 84, 69, 116, 101, 101, 84, 22, 54, 22, 22, 54, 22, 69, 54, 101, 22, 22, 20, 21, 22, 20, 52, 20, 21]
theorem block14 : ∀ u ∈ List.range 32, !valid5 (448+u) || check (word5 (448+u)) cert14[u]! = true := by decide +kernel
def cert15 : Array Nat := #[52, 52, 22, 20, 9, 9, 10, 13, 9, 26, 13, 9, 10, 26, 41, 9, 9, 11, 13, 9, 41, 13, 9, 11, 41, 41, 10, 11, 10, 42, 10, 26]
theorem block15 : ∀ u ∈ List.range 32, !valid5 (480+u) || check (word5 (480+u)) cert15[u]! = true := by decide +kernel

theorem portion1 (h : Nat) (lo : 256≤h) (hi : h<512) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t12 : h<384
  ·
    by_cases t10 : h<320
    ·
      by_cases t9 : h<288
      ·
        have H := block8 (h-256) (List.mem_range.mpr (by omega))
        have E : 256+(h-256)=h := by omega
        rw [E,valid] at H
        exact ⟨cert8[h-256]!,by simpa using H⟩
      ·
        have H := block9 (h-288) (List.mem_range.mpr (by omega))
        have E : 288+(h-288)=h := by omega
        rw [E,valid] at H
        exact ⟨cert9[h-288]!,by simpa using H⟩
    ·
      by_cases t11 : h<352
      ·
        have H := block10 (h-320) (List.mem_range.mpr (by omega))
        have E : 320+(h-320)=h := by omega
        rw [E,valid] at H
        exact ⟨cert10[h-320]!,by simpa using H⟩
      ·
        have H := block11 (h-352) (List.mem_range.mpr (by omega))
        have E : 352+(h-352)=h := by omega
        rw [E,valid] at H
        exact ⟨cert11[h-352]!,by simpa using H⟩
  ·
    by_cases t14 : h<448
    ·
      by_cases t13 : h<416
      ·
        have H := block12 (h-384) (List.mem_range.mpr (by omega))
        have E : 384+(h-384)=h := by omega
        rw [E,valid] at H
        exact ⟨cert12[h-384]!,by simpa using H⟩
      ·
        have H := block13 (h-416) (List.mem_range.mpr (by omega))
        have E : 416+(h-416)=h := by omega
        rw [E,valid] at H
        exact ⟨cert13[h-416]!,by simpa using H⟩
    ·
      by_cases t15 : h<480
      ·
        have H := block14 (h-448) (List.mem_range.mpr (by omega))
        have E : 448+(h-448)=h := by omega
        rw [E,valid] at H
        exact ⟨cert14[h-448]!,by simpa using H⟩
      ·
        have H := block15 (h-480) (List.mem_range.mpr (by omega))
        have E : 480+(h-480)=h := by omega
        rw [E,valid] at H
        exact ⟨cert15[h-480]!,by simpa using H⟩
end BikovEight
