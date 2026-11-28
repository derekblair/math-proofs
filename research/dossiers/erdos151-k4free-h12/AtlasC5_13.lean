import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert104 : Array Nat := #[50, 50, 52, 0, 0, 53, 114, 53, 114, 53, 0, 114, 114, 53, 0, 0, 114, 114, 116, 114, 114, 0, 114, 114, 116, 0, 0, 58, 58, 116, 58, 116]
theorem block104 : ∀ u ∈ List.range 32, !valid5 (3328+u) || check (word5 (3328+u)) cert104[u]! = true := by decide +kernel
def cert105 : Array Nat := #[0, 58, 116, 116, 0, 0, 50, 50, 25857528, 50, 50, 0, 50, 50, 70225321, 0, 0, 52, 52, 52, 42384696, 52, 0, 71548265, 52, 52, 0, 0, 37, 0, 37, 0]
theorem block105 : ∀ u ∈ List.range 32, !valid5 (3360+u) || check (word5 (3360+u)) cert105[u]! = true := by decide +kernel
def cert106 : Array Nat := #[37, 37, 0, 0, 37, 37, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 101, 0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 37, 0, 37]
theorem block106 : ∀ u ∈ List.range 32, !valid5 (3392+u) || check (word5 (3392+u)) cert106[u]! = true := by decide +kernel
def cert107 : Array Nat := #[0, 37, 37, 0, 0, 37, 37, 0, 45, 0, 45, 0, 101, 45, 0, 0, 101, 45, 0, 53, 0, 53, 0, 53, 101, 0, 0, 53, 101, 0, 37, 0]
theorem block107 : ∀ u ∈ List.range 32, !valid5 (3424+u) || check (word5 (3424+u)) cert107[u]! = true := by decide +kernel
def cert108 : Array Nat := #[37, 0, 37, 37, 0, 0, 37, 37, 0, 45, 0, 45, 0, 51039609, 45, 0, 0, 51039610, 45, 0, 101, 0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 101]
theorem block108 : ∀ u ∈ List.range 32, !valid5 (3456+u) || check (word5 (3456+u)) cert108[u]! = true := by decide +kernel
def cert109 : Array Nat := #[0, 101, 0, 101, 101, 0, 0, 101, 101, 0, 53, 0, 53, 0, 53, 71482745, 0, 0, 53, 71482746, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41]
theorem block109 : ∀ u ∈ List.range 32, !valid5 (3488+u) || check (word5 (3488+u)) cert109[u]! = true := by decide +kernel
def cert110 : Array Nat := #[41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 43, 0, 105, 43, 0, 43, 0, 0, 0, 105, 43, 45, 0, 45, 105, 0, 45, 0, 0, 0, 45]
theorem block110 : ∀ u ∈ List.range 32, !valid5 (3520+u) || check (word5 (3520+u)) cert110[u]! = true := by decide +kernel
def cert111 : Array Nat := #[105, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 105, 0, 105, 105, 0, 105, 0, 0, 0, 105, 105, 45, 0, 45, 34512441, 0, 45, 0, 0, 0]
theorem block111 : ∀ u ∈ List.range 32, !valid5 (3552+u) || check (word5 (3552+u)) cert111[u]! = true := by decide +kernel

theorem portion13 (h : Nat) (lo : 3328≤h) (hi : h<3584) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t108 : h<3456
  ·
    by_cases t106 : h<3392
    ·
      by_cases t105 : h<3360
      ·
        have H := block104 (h-3328) (List.mem_range.mpr (by omega))
        have E : 3328+(h-3328)=h := by omega
        rw [E,valid] at H
        exact ⟨cert104[h-3328]!,by simpa using H⟩
      ·
        have H := block105 (h-3360) (List.mem_range.mpr (by omega))
        have E : 3360+(h-3360)=h := by omega
        rw [E,valid] at H
        exact ⟨cert105[h-3360]!,by simpa using H⟩
    ·
      by_cases t107 : h<3424
      ·
        have H := block106 (h-3392) (List.mem_range.mpr (by omega))
        have E : 3392+(h-3392)=h := by omega
        rw [E,valid] at H
        exact ⟨cert106[h-3392]!,by simpa using H⟩
      ·
        have H := block107 (h-3424) (List.mem_range.mpr (by omega))
        have E : 3424+(h-3424)=h := by omega
        rw [E,valid] at H
        exact ⟨cert107[h-3424]!,by simpa using H⟩
  ·
    by_cases t110 : h<3520
    ·
      by_cases t109 : h<3488
      ·
        have H := block108 (h-3456) (List.mem_range.mpr (by omega))
        have E : 3456+(h-3456)=h := by omega
        rw [E,valid] at H
        exact ⟨cert108[h-3456]!,by simpa using H⟩
      ·
        have H := block109 (h-3488) (List.mem_range.mpr (by omega))
        have E : 3488+(h-3488)=h := by omega
        rw [E,valid] at H
        exact ⟨cert109[h-3488]!,by simpa using H⟩
    ·
      by_cases t111 : h<3552
      ·
        have H := block110 (h-3520) (List.mem_range.mpr (by omega))
        have E : 3520+(h-3520)=h := by omega
        rw [E,valid] at H
        exact ⟨cert110[h-3520]!,by simpa using H⟩
      ·
        have H := block111 (h-3552) (List.mem_range.mpr (by omega))
        have E : 3552+(h-3552)=h := by omega
        rw [E,valid] at H
        exact ⟨cert111[h-3552]!,by simpa using H⟩
end BikovEight
