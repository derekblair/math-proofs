import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert288 : Array Nat := #[0, 0, 116, 116, 116, 0, 116, 0, 0, 116, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 116, 116, 0, 116, 0, 0, 116]
theorem block288 : ∀ u ∈ List.range 32, !valid5 (9216+u) || check (word5 (9216+u)) cert288[u]! = true := by decide +kernel
def cert289 : Array Nat := #[116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 116, 116, 0, 116, 0, 0]
theorem block289 : ∀ u ∈ List.range 32, !valid5 (9248+u) || check (word5 (9248+u)) cert289[u]! = true := by decide +kernel
def cert290 : Array Nat := #[116, 116, 0, 0, 116, 116, 116, 0, 116, 0, 0, 116, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block290 : ∀ u ∈ List.range 32, !valid5 (9280+u) || check (word5 (9280+u)) cert290[u]! = true := by decide +kernel
def cert291 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block291 : ∀ u ∈ List.range 32, !valid5 (9312+u) || check (word5 (9312+u)) cert291[u]! = true := by decide +kernel
def cert292 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block292 : ∀ u ∈ List.range 32, !valid5 (9344+u) || check (word5 (9344+u)) cert292[u]! = true := by decide +kernel
def cert293 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block293 : ∀ u ∈ List.range 32, !valid5 (9376+u) || check (word5 (9376+u)) cert293[u]! = true := by decide +kernel
def cert294 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block294 : ∀ u ∈ List.range 32, !valid5 (9408+u) || check (word5 (9408+u)) cert294[u]! = true := by decide +kernel
def cert295 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block295 : ∀ u ∈ List.range 32, !valid5 (9440+u) || check (word5 (9440+u)) cert295[u]! = true := by decide +kernel

theorem portion36 (h : Nat) (lo : 9216≤h) (hi : h<9472) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t292 : h<9344
  ·
    by_cases t290 : h<9280
    ·
      by_cases t289 : h<9248
      ·
        have H := block288 (h-9216) (List.mem_range.mpr (by omega))
        have E : 9216+(h-9216)=h := by omega
        rw [E,valid] at H
        exact ⟨cert288[h-9216]!,by simpa using H⟩
      ·
        have H := block289 (h-9248) (List.mem_range.mpr (by omega))
        have E : 9248+(h-9248)=h := by omega
        rw [E,valid] at H
        exact ⟨cert289[h-9248]!,by simpa using H⟩
    ·
      by_cases t291 : h<9312
      ·
        have H := block290 (h-9280) (List.mem_range.mpr (by omega))
        have E : 9280+(h-9280)=h := by omega
        rw [E,valid] at H
        exact ⟨cert290[h-9280]!,by simpa using H⟩
      ·
        have H := block291 (h-9312) (List.mem_range.mpr (by omega))
        have E : 9312+(h-9312)=h := by omega
        rw [E,valid] at H
        exact ⟨cert291[h-9312]!,by simpa using H⟩
  ·
    by_cases t294 : h<9408
    ·
      by_cases t293 : h<9376
      ·
        have H := block292 (h-9344) (List.mem_range.mpr (by omega))
        have E : 9344+(h-9344)=h := by omega
        rw [E,valid] at H
        exact ⟨cert292[h-9344]!,by simpa using H⟩
      ·
        have H := block293 (h-9376) (List.mem_range.mpr (by omega))
        have E : 9376+(h-9376)=h := by omega
        rw [E,valid] at H
        exact ⟨cert293[h-9376]!,by simpa using H⟩
    ·
      by_cases t295 : h<9440
      ·
        have H := block294 (h-9408) (List.mem_range.mpr (by omega))
        have E : 9408+(h-9408)=h := by omega
        rw [E,valid] at H
        exact ⟨cert294[h-9408]!,by simpa using H⟩
      ·
        have H := block295 (h-9440) (List.mem_range.mpr (by omega))
        have E : 9440+(h-9440)=h := by omega
        rw [E,valid] at H
        exact ⟨cert295[h-9440]!,by simpa using H⟩
end BikovEight
