import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert16 : Array Nat := #[42, 11, 10, 26, 42, 13, 13, 45, 13, 13, 45, 13, 13, 74, 45, 105, 9, 9, 10, 13, 9, 26, 13, 9, 10, 26, 41, 26, 58, 26, 58, 26]
theorem block16 : ∀ u ∈ List.range 32, !valid5 (512+u) || check (word5 (512+u)) cert16[u]! = true := by decide +kernel
def cert17 : Array Nat := #[26, 58, 73, 26, 26, 105, 13, 13, 45, 13, 13, 45, 13, 13, 74, 45, 106, 9, 9, 11, 13, 9, 41, 13, 9, 11, 41, 41, 10, 11, 10, 42]
theorem block17 : ∀ u ∈ List.range 32, !valid5 (544+u) || check (word5 (544+u)) cert17[u]! = true := by decide +kernel
def cert18 : Array Nat := #[10, 26, 42, 11, 10, 26, 42, 26, 58, 26, 58, 26, 26, 58, 73, 26, 26, 105, 73, 73, 74, 105, 73, 105, 106, 73, 74, 105, 105, 18, 21, 18]
theorem block18 : ∀ u ∈ List.range 32, !valid5 (576+u) || check (word5 (576+u)) cert18[u]! = true := by decide +kernel
def cert19 : Array Nat := #[20, 26, 18, 21, 50, 26, 18, 20, 21, 21, 53, 21, 53, 21, 21, 114, 53, 82, 21, 18, 50, 18, 22, 26, 18, 50, 50, 26, 18, 22, 20, 21]
theorem block19 : ∀ u ∈ List.range 32, !valid5 (608+u) || check (word5 (608+u)) cert19[u]! = true := by decide +kernel
def cert20 : Array Nat := #[22, 20, 52, 20, 21, 52, 52, 22, 20, 26, 58, 26, 58, 26, 26, 58, 114, 26, 26, 84, 18, 21, 18, 20, 26, 18, 21, 50, 26, 18, 20, 21]
theorem block20 : ∀ u ∈ List.range 32, !valid5 (640+u) || check (word5 (640+u)) cert20[u]! = true := by decide +kernel
def cert21 : Array Nat := #[21, 53, 21, 53, 21, 21, 114, 53, 82, 21, 82, 114, 82, 84, 114, 82, 114, 114, 116, 82, 84, 26, 58, 26, 58, 26, 26, 58, 116, 26, 26, 84]
theorem block21 : ∀ u ∈ List.range 32, !valid5 (672+u) || check (word5 (672+u)) cert21[u]! = true := by decide +kernel
def cert22 : Array Nat := #[18, 50, 18, 22, 26, 18, 50, 50, 26, 18, 22, 20, 21, 22, 20, 52, 20, 21, 52, 52, 22, 20, 5, 5, 37, 5, 13, 21, 5, 13, 37, 37]
theorem block22 : ∀ u ∈ List.range 32, !valid5 (704+u) || check (word5 (704+u)) cert22[u]! = true := by decide +kernel
def cert23 : Array Nat := #[21, 5, 5, 37, 5, 13, 21, 5, 13, 37, 37, 21, 69, 69, 101, 69, 77, 85, 69, 77, 101, 101, 85, 5, 5, 37, 5, 13, 21, 5, 13, 37]
theorem block23 : ∀ u ∈ List.range 32, !valid5 (736+u) || check (word5 (736+u)) cert23[u]! = true := by decide +kernel

theorem portion2 (h : Nat) (lo : 512≤h) (hi : h<768) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t20 : h<640
  ·
    by_cases t18 : h<576
    ·
      by_cases t17 : h<544
      ·
        have H := block16 (h-512) (List.mem_range.mpr (by omega))
        have E : 512+(h-512)=h := by omega
        rw [E,valid] at H
        exact ⟨cert16[h-512]!,by simpa using H⟩
      ·
        have H := block17 (h-544) (List.mem_range.mpr (by omega))
        have E : 544+(h-544)=h := by omega
        rw [E,valid] at H
        exact ⟨cert17[h-544]!,by simpa using H⟩
    ·
      by_cases t19 : h<608
      ·
        have H := block18 (h-576) (List.mem_range.mpr (by omega))
        have E : 576+(h-576)=h := by omega
        rw [E,valid] at H
        exact ⟨cert18[h-576]!,by simpa using H⟩
      ·
        have H := block19 (h-608) (List.mem_range.mpr (by omega))
        have E : 608+(h-608)=h := by omega
        rw [E,valid] at H
        exact ⟨cert19[h-608]!,by simpa using H⟩
  ·
    by_cases t22 : h<704
    ·
      by_cases t21 : h<672
      ·
        have H := block20 (h-640) (List.mem_range.mpr (by omega))
        have E : 640+(h-640)=h := by omega
        rw [E,valid] at H
        exact ⟨cert20[h-640]!,by simpa using H⟩
      ·
        have H := block21 (h-672) (List.mem_range.mpr (by omega))
        have E : 672+(h-672)=h := by omega
        rw [E,valid] at H
        exact ⟨cert21[h-672]!,by simpa using H⟩
    ·
      by_cases t23 : h<736
      ·
        have H := block22 (h-704) (List.mem_range.mpr (by omega))
        have E : 704+(h-704)=h := by omega
        rw [E,valid] at H
        exact ⟨cert22[h-704]!,by simpa using H⟩
      ·
        have H := block23 (h-736) (List.mem_range.mpr (by omega))
        have E : 736+(h-736)=h := by omega
        rw [E,valid] at H
        exact ⟨cert23[h-736]!,by simpa using H⟩
end BikovEight
