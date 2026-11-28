import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert240 : Array Nat := #[74, 73160565, 74, 0, 35232830, 75, 74, 0, 0, 74, 0, 74, 0, 74, 90, 0, 0, 74, 90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block240 : ∀ u ∈ List.range 32, !valid5 (7680+u) || check (word5 (7680+u)) cert240[u]! = true := by decide +kernel
def cert241 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 75, 74, 0, 74, 0, 0, 75, 74, 0, 0]
theorem block241 : ∀ u ∈ List.range 32, !valid5 (7712+u) || check (word5 (7712+u)) cert241[u]! = true := by decide +kernel
def cert242 : Array Nat := #[82, 26571252, 82, 86, 90, 82, 77980093, 28402173, 90, 82, 86, 82, 0, 82, 86, 90, 82, 0, 0, 90, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block242 : ∀ u ∈ List.range 32, !valid5 (7744+u) || check (word5 (7744+u)) cert242[u]! = true := by decide +kernel
def cert243 : Array Nat := #[0, 82, 35509301, 82, 0, 90, 82, 0, 7916478, 90, 82, 0, 82, 52255093, 82, 86, 0, 82, 5905406, 0, 0, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block243 : ∀ u ∈ List.range 32, !valid5 (7776+u) || check (word5 (7776+u)) cert243[u]! = true := by decide +kernel
def cert244 : Array Nat := #[0, 0, 82, 0, 82, 0, 90, 82, 0, 0, 90, 82, 0, 82, 0, 82, 86, 0, 82, 0, 0, 0, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block244 : ∀ u ∈ List.range 32, !valid5 (7808+u) || check (word5 (7808+u)) cert244[u]! = true := by decide +kernel
def cert245 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 85, 86, 84, 72644468, 84, 85]
theorem block245 : ∀ u ∈ List.range 32, !valid5 (7840+u) || check (word5 (7840+u)) cert245[u]! = true := by decide +kernel
def cert246 : Array Nat := #[45147965, 78145405, 86, 84, 84, 0, 86, 84, 8182197, 84, 0, 0, 11166718, 86, 84, 84, 85, 0, 84, 24925749, 84, 85, 28402174, 0, 0, 84, 0, 0, 0, 0, 0, 0]
theorem block246 : ∀ u ∈ List.range 32, !valid5 (7872+u) || check (word5 (7872+u)) cert246[u]! = true := by decide +kernel
def cert247 : Array Nat := #[0, 0, 0, 0, 0, 84, 85, 86, 84, 0, 84, 85, 0, 0, 86, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block247 : ∀ u ∈ List.range 32, !valid5 (7904+u) || check (word5 (7904+u)) cert247[u]! = true := by decide +kernel

theorem portion30 (h : Nat) (lo : 7680≤h) (hi : h<7936) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t244 : h<7808
  ·
    by_cases t242 : h<7744
    ·
      by_cases t241 : h<7712
      ·
        have H := block240 (h-7680) (List.mem_range.mpr (by omega))
        have E : 7680+(h-7680)=h := by omega
        rw [E,valid] at H
        exact ⟨cert240[h-7680]!,by simpa using H⟩
      ·
        have H := block241 (h-7712) (List.mem_range.mpr (by omega))
        have E : 7712+(h-7712)=h := by omega
        rw [E,valid] at H
        exact ⟨cert241[h-7712]!,by simpa using H⟩
    ·
      by_cases t243 : h<7776
      ·
        have H := block242 (h-7744) (List.mem_range.mpr (by omega))
        have E : 7744+(h-7744)=h := by omega
        rw [E,valid] at H
        exact ⟨cert242[h-7744]!,by simpa using H⟩
      ·
        have H := block243 (h-7776) (List.mem_range.mpr (by omega))
        have E : 7776+(h-7776)=h := by omega
        rw [E,valid] at H
        exact ⟨cert243[h-7776]!,by simpa using H⟩
  ·
    by_cases t246 : h<7872
    ·
      by_cases t245 : h<7840
      ·
        have H := block244 (h-7808) (List.mem_range.mpr (by omega))
        have E : 7808+(h-7808)=h := by omega
        rw [E,valid] at H
        exact ⟨cert244[h-7808]!,by simpa using H⟩
      ·
        have H := block245 (h-7840) (List.mem_range.mpr (by omega))
        have E : 7840+(h-7840)=h := by omega
        rw [E,valid] at H
        exact ⟨cert245[h-7840]!,by simpa using H⟩
    ·
      by_cases t247 : h<7904
      ·
        have H := block246 (h-7872) (List.mem_range.mpr (by omega))
        have E : 7872+(h-7872)=h := by omega
        rw [E,valid] at H
        exact ⟨cert246[h-7872]!,by simpa using H⟩
      ·
        have H := block247 (h-7904) (List.mem_range.mpr (by omega))
        have E : 7904+(h-7904)=h := by omega
        rw [E,valid] at H
        exact ⟨cert247[h-7904]!,by simpa using H⟩
end BikovEight
