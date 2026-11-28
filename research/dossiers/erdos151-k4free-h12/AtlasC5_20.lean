import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert160 : Array Nat := #[0, 0, 54, 0, 0, 0, 58, 58, 0, 58, 0, 0, 58, 0, 0, 0, 0, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 80073149, 0, 0, 0]
theorem block160 : ∀ u ∈ List.range 32, !valid5 (5120+u) || check (word5 (5120+u)) cert160[u]! = true := by decide +kernel
def cert161 : Array Nat := #[5643774, 0, 0, 0, 0, 0, 0, 30495229, 0, 0, 7654846, 0, 0, 0, 0, 0, 0, 0, 58, 58, 0, 58, 0, 0, 58, 0, 0, 0, 0, 50, 50, 0]
theorem block161 : ∀ u ∈ List.range 32, !valid5 (5152+u) || check (word5 (5152+u)) cert161[u]! = true := by decide +kernel
def cert162 : Array Nat := #[50, 50, 0, 50, 50, 0, 0, 0, 54, 54, 0, 0, 54, 0, 0, 54, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 53, 0]
theorem block162 : ∀ u ∈ List.range 32, !valid5 (5184+u) || check (word5 (5184+u)) cert162[u]! = true := by decide +kernel
def cert163 : Array Nat := #[53, 0, 53, 0, 0, 0, 53, 0, 0, 54, 54, 0, 0, 54, 0, 0, 54, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 72630132]
theorem block163 : ∀ u ∈ List.range 32, !valid5 (5216+u) || check (word5 (5216+u)) cert163[u]! = true := by decide +kernel
def cert164 : Array Nat := #[8186285, 24929837, 0, 0, 0, 0, 0, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 53, 0, 53, 0, 53, 0, 0, 0, 53, 0, 0]
theorem block164 : ∀ u ∈ List.range 32, !valid5 (5248+u) || check (word5 (5248+u)) cert164[u]! = true := by decide +kernel
def cert165 : Array Nat := #[47241021, 0, 30495230, 0, 0, 0, 0, 0, 0, 0, 0, 80238461, 13259774, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 54, 0, 0, 54, 0, 0, 54, 0, 0]
theorem block165 : ∀ u ∈ List.range 32, !valid5 (5280+u) || check (word5 (5280+u)) cert165[u]! = true := by decide +kernel
def cert166 : Array Nat := #[0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 69, 69, 74, 69, 73, 82, 69, 73, 74, 82, 84, 74, 106, 74, 84, 74, 82, 106, 114, 74]
theorem block166 : ∀ u ∈ List.range 32, !valid5 (5312+u) || check (word5 (5312+u)) cert166[u]! = true := by decide +kernel
def cert167 : Array Nat := #[82, 84, 69, 69, 101, 69, 73, 84, 69, 73, 101, 101, 84, 73, 73, 74, 105, 73, 82, 106, 73, 74, 82, 105, 69, 69, 82, 69, 101, 82, 69, 114]
theorem block167 : ∀ u ∈ List.range 32, !valid5 (5344+u) || check (word5 (5344+u)) cert167[u]! = true := by decide +kernel

theorem portion20 (h : Nat) (lo : 5120≤h) (hi : h<5376) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t164 : h<5248
  ·
    by_cases t162 : h<5184
    ·
      by_cases t161 : h<5152
      ·
        have H := block160 (h-5120) (List.mem_range.mpr (by omega))
        have E : 5120+(h-5120)=h := by omega
        rw [E,valid] at H
        exact ⟨cert160[h-5120]!,by simpa using H⟩
      ·
        have H := block161 (h-5152) (List.mem_range.mpr (by omega))
        have E : 5152+(h-5152)=h := by omega
        rw [E,valid] at H
        exact ⟨cert161[h-5152]!,by simpa using H⟩
    ·
      by_cases t163 : h<5216
      ·
        have H := block162 (h-5184) (List.mem_range.mpr (by omega))
        have E : 5184+(h-5184)=h := by omega
        rw [E,valid] at H
        exact ⟨cert162[h-5184]!,by simpa using H⟩
      ·
        have H := block163 (h-5216) (List.mem_range.mpr (by omega))
        have E : 5216+(h-5216)=h := by omega
        rw [E,valid] at H
        exact ⟨cert163[h-5216]!,by simpa using H⟩
  ·
    by_cases t166 : h<5312
    ·
      by_cases t165 : h<5280
      ·
        have H := block164 (h-5248) (List.mem_range.mpr (by omega))
        have E : 5248+(h-5248)=h := by omega
        rw [E,valid] at H
        exact ⟨cert164[h-5248]!,by simpa using H⟩
      ·
        have H := block165 (h-5280) (List.mem_range.mpr (by omega))
        have E : 5280+(h-5280)=h := by omega
        rw [E,valid] at H
        exact ⟨cert165[h-5280]!,by simpa using H⟩
    ·
      by_cases t167 : h<5344
      ·
        have H := block166 (h-5312) (List.mem_range.mpr (by omega))
        have E : 5312+(h-5312)=h := by omega
        rw [E,valid] at H
        exact ⟨cert166[h-5312]!,by simpa using H⟩
      ·
        have H := block167 (h-5344) (List.mem_range.mpr (by omega))
        have E : 5344+(h-5344)=h := by omega
        rw [E,valid] at H
        exact ⟨cert167[h-5344]!,by simpa using H⟩
end BikovEight
