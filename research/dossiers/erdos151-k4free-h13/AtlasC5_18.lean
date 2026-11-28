import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert144 : Array Nat := #[0, 53, 0, 53, 5413051, 53, 0, 0, 0, 53, 0, 0, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52]
theorem block144 : ∀ u ∈ List.range 32, !valid5 (4608+u) || check (word5 (4608+u)) cert144[u]! = true := by decide +kernel
def cert145 : Array Nat := #[0, 0, 58, 58, 53650107, 58, 0, 0, 58, 0, 0, 0, 0, 50, 50, 52, 50, 50, 0, 50, 50, 52, 0, 0, 53, 0, 53, 0, 53, 0, 0, 0]
theorem block145 : ∀ u ∈ List.range 32, !valid5 (4640+u) || check (word5 (4640+u)) cert145[u]! = true := by decide +kernel
def cert146 : Array Nat := #[53, 0, 0, 7654844, 0, 26833389, 43579181, 0, 0, 0, 0, 0, 0, 0, 58, 58, 0, 58, 0, 0, 58, 0, 0, 0, 0, 50, 50, 0, 50, 50, 0, 50]
theorem block146 : ∀ u ∈ List.range 32, !valid5 (4672+u) || check (word5 (4672+u)) cert146[u]! = true := by decide +kernel
def cert147 : Array Nat := #[50, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 37, 0, 37, 0, 37, 37]
theorem block147 : ∀ u ∈ List.range 32, !valid5 (4704+u) || check (word5 (4704+u)) cert147[u]! = true := by decide +kernel
def cert148 : Array Nat := #[0, 0, 37, 37, 0, 34971700, 0, 0, 0, 54420781, 71164333, 0, 0, 0, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 45, 0, 45, 0, 0]
theorem block148 : ∀ u ∈ List.range 32, !valid5 (4736+u) || check (word5 (4736+u)) cert148[u]! = true := by decide +kernel
def cert149 : Array Nat := #[45, 0, 0, 0, 45, 0, 53, 0, 53, 0, 53, 0, 0, 0, 53, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 45, 0, 45, 0]
theorem block149 : ∀ u ∈ List.range 32, !valid5 (4768+u) || check (word5 (4768+u)) cert149[u]! = true := by decide +kernel
def cert150 : Array Nat := #[0, 45, 0, 0, 0, 45, 0, 13259773, 0, 0, 0, 0, 24391230, 0, 0, 0, 0, 0, 46257213, 0, 0, 0, 26545662, 0, 0, 0, 0, 0, 0, 53, 0, 53]
theorem block150 : ∀ u ∈ List.range 32, !valid5 (4800+u) || check (word5 (4800+u)) cert150[u]! = true := by decide +kernel
def cert151 : Array Nat := #[0, 53, 0, 0, 0, 53, 0, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 43, 0]
theorem block151 : ∀ u ∈ List.range 32, !valid5 (4832+u) || check (word5 (4832+u)) cert151[u]! = true := by decide +kernel

theorem portion18 (h : Nat) (lo : 4608≤h) (hi : h<4864) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t148 : h<4736
  ·
    by_cases t146 : h<4672
    ·
      by_cases t145 : h<4640
      ·
        have H := block144 (h-4608) (List.mem_range.mpr (by omega))
        have E : 4608+(h-4608)=h := by omega
        rw [E,valid] at H
        exact ⟨cert144[h-4608]!,by simpa using H⟩
      ·
        have H := block145 (h-4640) (List.mem_range.mpr (by omega))
        have E : 4640+(h-4640)=h := by omega
        rw [E,valid] at H
        exact ⟨cert145[h-4640]!,by simpa using H⟩
    ·
      by_cases t147 : h<4704
      ·
        have H := block146 (h-4672) (List.mem_range.mpr (by omega))
        have E : 4672+(h-4672)=h := by omega
        rw [E,valid] at H
        exact ⟨cert146[h-4672]!,by simpa using H⟩
      ·
        have H := block147 (h-4704) (List.mem_range.mpr (by omega))
        have E : 4704+(h-4704)=h := by omega
        rw [E,valid] at H
        exact ⟨cert147[h-4704]!,by simpa using H⟩
  ·
    by_cases t150 : h<4800
    ·
      by_cases t149 : h<4768
      ·
        have H := block148 (h-4736) (List.mem_range.mpr (by omega))
        have E : 4736+(h-4736)=h := by omega
        rw [E,valid] at H
        exact ⟨cert148[h-4736]!,by simpa using H⟩
      ·
        have H := block149 (h-4768) (List.mem_range.mpr (by omega))
        have E : 4768+(h-4768)=h := by omega
        rw [E,valid] at H
        exact ⟨cert149[h-4768]!,by simpa using H⟩
    ·
      by_cases t151 : h<4832
      ·
        have H := block150 (h-4800) (List.mem_range.mpr (by omega))
        have E : 4800+(h-4800)=h := by omega
        rw [E,valid] at H
        exact ⟨cert150[h-4800]!,by simpa using H⟩
      ·
        have H := block151 (h-4832) (List.mem_range.mpr (by omega))
        have E : 4832+(h-4832)=h := by omega
        rw [E,valid] at H
        exact ⟨cert151[h-4832]!,by simpa using H⟩
end BikovEight
