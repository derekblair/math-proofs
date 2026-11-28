import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert112 : Array Nat := #[45, 34512442, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 43, 0, 23244345, 43, 0, 43, 0, 0, 0, 23244346, 43, 105, 0, 105, 105, 0, 105, 0, 0]
theorem block112 : ∀ u ∈ List.range 32, !valid5 (3584+u) || check (word5 (3584+u)) cert112[u]! = true := by decide +kernel
def cert113 : Array Nat := #[0, 105, 105, 105, 0, 105, 105, 0, 105, 0, 0, 0, 105, 105, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 43, 106, 0, 43, 0, 43, 106]
theorem block113 : ∀ u ∈ List.range 32, !valid5 (3616+u) || check (word5 (3616+u)) cert113[u]! = true := by decide +kernel
def cert114 : Array Nat := #[0, 0, 0, 43, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 106, 106, 0, 106, 0, 106, 106, 0, 0, 0, 106, 42, 42, 0, 42, 0, 42]
theorem block114 : ∀ u ∈ List.range 32, !valid5 (3648+u) || check (word5 (3648+u)) cert114[u]! = true := by decide +kernel
def cert115 : Array Nat := #[42, 0, 0, 0, 42, 58, 58, 0, 58, 0, 106, 58, 0, 0, 0, 106, 106, 106, 0, 106, 0, 106, 106, 0, 0, 0, 106, 43, 6737337, 0, 43, 0]
theorem block115 : ∀ u ∈ List.range 32, !valid5 (3680+u) || check (word5 (3680+u)) cert115[u]! = true := by decide +kernel
def cert116 : Array Nat := #[43, 6737338, 0, 0, 0, 43, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 58, 58, 0, 58, 0, 70159801, 58, 0, 0, 0, 70159802, 106, 106, 0, 106]
theorem block116 : ∀ u ∈ List.range 32, !valid5 (3712+u) || check (word5 (3712+u)) cert116[u]! = true := by decide +kernel
def cert117 : Array Nat := #[0, 106, 106, 0, 0, 0, 106, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 114, 114, 0, 114, 114, 0, 114, 114, 0, 0, 0, 50, 50, 0]
theorem block117 : ∀ u ∈ List.range 32, !valid5 (3744+u) || check (word5 (3744+u)) cert117[u]! = true := by decide +kernel
def cert118 : Array Nat := #[50, 50, 0, 50, 50, 0, 0, 0, 54, 54, 0, 114, 54, 0, 114, 54, 0, 0, 0, 58, 58, 0, 58, 114, 0, 58, 114, 0, 0, 0, 50, 50]
theorem block118 : ∀ u ∈ List.range 32, !valid5 (3776+u) || check (word5 (3776+u)) cert118[u]! = true := by decide +kernel
def cert119 : Array Nat := #[0, 50, 50, 0, 50, 50, 0, 0, 0, 114, 114, 0, 114, 114, 0, 114, 114, 0, 0, 0, 114, 114, 0, 114, 114, 0, 114, 114, 0, 0, 0, 58]
theorem block119 : ∀ u ∈ List.range 32, !valid5 (3808+u) || check (word5 (3808+u)) cert119[u]! = true := by decide +kernel

theorem portion14 (h : Nat) (lo : 3584≤h) (hi : h<3840) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t116 : h<3712
  ·
    by_cases t114 : h<3648
    ·
      by_cases t113 : h<3616
      ·
        have H := block112 (h-3584) (List.mem_range.mpr (by omega))
        have E : 3584+(h-3584)=h := by omega
        rw [E,valid] at H
        exact ⟨cert112[h-3584]!,by simpa using H⟩
      ·
        have H := block113 (h-3616) (List.mem_range.mpr (by omega))
        have E : 3616+(h-3616)=h := by omega
        rw [E,valid] at H
        exact ⟨cert113[h-3616]!,by simpa using H⟩
    ·
      by_cases t115 : h<3680
      ·
        have H := block114 (h-3648) (List.mem_range.mpr (by omega))
        have E : 3648+(h-3648)=h := by omega
        rw [E,valid] at H
        exact ⟨cert114[h-3648]!,by simpa using H⟩
      ·
        have H := block115 (h-3680) (List.mem_range.mpr (by omega))
        have E : 3680+(h-3680)=h := by omega
        rw [E,valid] at H
        exact ⟨cert115[h-3680]!,by simpa using H⟩
  ·
    by_cases t118 : h<3776
    ·
      by_cases t117 : h<3744
      ·
        have H := block116 (h-3712) (List.mem_range.mpr (by omega))
        have E : 3712+(h-3712)=h := by omega
        rw [E,valid] at H
        exact ⟨cert116[h-3712]!,by simpa using H⟩
      ·
        have H := block117 (h-3744) (List.mem_range.mpr (by omega))
        have E : 3744+(h-3744)=h := by omega
        rw [E,valid] at H
        exact ⟨cert117[h-3744]!,by simpa using H⟩
    ·
      by_cases t119 : h<3808
      ·
        have H := block118 (h-3776) (List.mem_range.mpr (by omega))
        have E : 3776+(h-3776)=h := by omega
        rw [E,valid] at H
        exact ⟨cert118[h-3776]!,by simpa using H⟩
      ·
        have H := block119 (h-3808) (List.mem_range.mpr (by omega))
        have E : 3808+(h-3808)=h := by omega
        rw [E,valid] at H
        exact ⟨cert119[h-3808]!,by simpa using H⟩
end BikovEight
