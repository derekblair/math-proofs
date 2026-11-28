import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert0 : Array Nat := #[5, 5, 10, 5, 9, 18, 5, 9, 10, 18, 20, 5, 5, 11, 5, 9, 21, 5, 9, 11, 37, 21, 10, 11, 10, 22, 10, 18, 42, 11, 10, 18]
theorem block0 : ∀ u ∈ List.range 32, !valid5 (0+u) || check (word5 (0+u)) cert0[u]! = true := by decide +kernel
def cert1 : Array Nat := #[22, 5, 5, 22, 5, 13, 20, 5, 13, 37, 22, 20, 9, 9, 10, 13, 9, 26, 13, 9, 10, 26, 41, 18, 21, 18, 20, 26, 18, 21, 50, 26]
theorem block1 : ∀ u ∈ List.range 32, !valid5 (32+u) || check (word5 (32+u)) cert1[u]! = true := by decide +kernel
def cert2 : Array Nat := #[18, 20, 5, 5, 37, 5, 13, 21, 5, 13, 37, 37, 21, 9, 9, 11, 13, 9, 41, 13, 9, 11, 41, 41, 10, 11, 10, 42, 10, 26, 42, 11]
theorem block2 : ∀ u ∈ List.range 32, !valid5 (64+u) || check (word5 (64+u)) cert2[u]! = true := by decide +kernel
def cert3 : Array Nat := #[10, 26, 42, 18, 50, 18, 22, 26, 18, 50, 50, 26, 18, 22, 20, 21, 22, 20, 52, 20, 21, 52, 52, 22, 20, 5, 5, 11, 5, 9, 21, 5]
theorem block3 : ∀ u ∈ List.range 32, !valid5 (96+u) || check (word5 (96+u)) cert3[u]! = true := by decide +kernel
def cert4 : Array Nat := #[9, 11, 37, 21, 5, 5, 11, 5, 9, 21, 5, 9, 11, 37, 21, 11, 11, 11, 43, 11, 43, 69, 11, 11, 101, 43, 5, 5, 37, 5, 13, 21]
theorem block4 : ∀ u ∈ List.range 32, !valid5 (128+u) || check (word5 (128+u)) cert4[u]! = true := by decide +kernel
def cert5 : Array Nat := #[5, 13, 37, 37, 21, 9, 9, 11, 13, 9, 41, 13, 9, 11, 41, 41, 21, 21, 53, 21, 53, 21, 21, 73, 53, 101, 21, 5, 5, 37, 5, 13]
theorem block5 : ∀ u ∈ List.range 32, !valid5 (160+u) || check (word5 (160+u)) cert5[u]! = true := by decide +kernel
def cert6 : Array Nat := #[21, 5, 13, 37, 37, 21, 9, 9, 11, 13, 9, 41, 13, 9, 11, 41, 41, 11, 11, 11, 43, 11, 43, 69, 11, 11, 101, 43, 69, 69, 101, 69]
theorem block6 : ∀ u ∈ List.range 32, !valid5 (192+u) || check (word5 (192+u)) cert6[u]! = true := by decide +kernel
def cert7 : Array Nat := #[73, 101, 69, 73, 101, 101, 105, 21, 21, 53, 21, 53, 21, 21, 73, 53, 105, 21, 10, 11, 10, 22, 10, 18, 42, 11, 10, 18, 22, 11, 11, 11]
theorem block7 : ∀ u ∈ List.range 32, !valid5 (224+u) || check (word5 (224+u)) cert7[u]! = true := by decide +kernel

theorem portion0 (h : Nat) (lo : 0≤h) (hi : h<256) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t4 : h<128
  ·
    by_cases t2 : h<64
    ·
      by_cases t1 : h<32
      ·
        have H := block0 (h-0) (List.mem_range.mpr (by omega))
        have E : 0+(h-0)=h := by omega
        rw [E,valid] at H
        exact ⟨cert0[h-0]!,by simpa using H⟩
      ·
        have H := block1 (h-32) (List.mem_range.mpr (by omega))
        have E : 32+(h-32)=h := by omega
        rw [E,valid] at H
        exact ⟨cert1[h-32]!,by simpa using H⟩
    ·
      by_cases t3 : h<96
      ·
        have H := block2 (h-64) (List.mem_range.mpr (by omega))
        have E : 64+(h-64)=h := by omega
        rw [E,valid] at H
        exact ⟨cert2[h-64]!,by simpa using H⟩
      ·
        have H := block3 (h-96) (List.mem_range.mpr (by omega))
        have E : 96+(h-96)=h := by omega
        rw [E,valid] at H
        exact ⟨cert3[h-96]!,by simpa using H⟩
  ·
    by_cases t6 : h<192
    ·
      by_cases t5 : h<160
      ·
        have H := block4 (h-128) (List.mem_range.mpr (by omega))
        have E : 128+(h-128)=h := by omega
        rw [E,valid] at H
        exact ⟨cert4[h-128]!,by simpa using H⟩
      ·
        have H := block5 (h-160) (List.mem_range.mpr (by omega))
        have E : 160+(h-160)=h := by omega
        rw [E,valid] at H
        exact ⟨cert5[h-160]!,by simpa using H⟩
    ·
      by_cases t7 : h<224
      ·
        have H := block6 (h-192) (List.mem_range.mpr (by omega))
        have E : 192+(h-192)=h := by omega
        rw [E,valid] at H
        exact ⟨cert6[h-192]!,by simpa using H⟩
      ·
        have H := block7 (h-224) (List.mem_range.mpr (by omega))
        have E : 224+(h-224)=h := by omega
        rw [E,valid] at H
        exact ⟨cert7[h-224]!,by simpa using H⟩
end BikovEight
