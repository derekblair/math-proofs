import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert136 : Array Nat := #[54, 0, 0, 0, 37, 52, 37, 0, 37, 37, 0, 52, 37, 37, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 54, 54, 0, 0, 54, 25856187]
theorem block136 : ∀ u ∈ List.range 32, !valid5 (4352+u) || check (word5 (4352+u)) cert136[u]! = true := by decide +kernel
def cert137 : Array Nat := #[0, 54, 0, 0, 0, 37, 52, 37, 0, 37, 37, 0, 52, 37, 37, 0, 45, 51037371, 45, 0, 0, 45, 0, 0, 0, 45, 0, 52, 52, 52, 0, 52]
theorem block137 : ∀ u ∈ List.range 32, !valid5 (4384+u) || check (word5 (4384+u)) cert137[u]! = true := by decide +kernel
def cert138 : Array Nat := #[0, 0, 52, 52, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 45, 0, 45, 0, 0, 45, 0, 0, 0, 45, 0, 24391228, 5927917, 0, 0]
theorem block138 : ∀ u ∈ List.range 32, !valid5 (4416+u) || check (word5 (4416+u)) cert138[u]! = true := by decide +kernel
def cert139 : Array Nat := #[0, 72906605, 0, 0, 0, 0, 0, 54, 54, 0, 0, 54, 0, 0, 54, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 41, 42, 41]
theorem block139 : ∀ u ∈ List.range 32, !valid5 (4448+u) || check (word5 (4448+u)) cert139[u]! = true := by decide +kernel
def cert140 : Array Nat := #[41, 0, 41, 42, 0, 0, 41, 41, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 45, 34511547]
theorem block140 : ∀ u ∈ List.range 32, !valid5 (4480+u) || check (word5 (4480+u)) cert140[u]! = true := by decide +kernel
def cert141 : Array Nat := #[45, 0, 0, 45, 0, 0, 0, 45, 0, 41, 42, 41, 41, 0, 41, 42, 0, 0, 41, 41, 58, 58, 70158011, 58, 0, 0, 58, 0, 0, 0, 0, 45]
theorem block141 : ∀ u ∈ List.range 32, !valid5 (4512+u) || check (word5 (4512+u)) cert141[u]! = true := by decide +kernel
def cert142 : Array Nat := #[0, 45, 0, 0, 45, 0, 0, 0, 45, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42]
theorem block142 : ∀ u ∈ List.range 32, !valid5 (4544+u) || check (word5 (4544+u)) cert142[u]! = true := by decide +kernel
def cert143 : Array Nat := #[58, 58, 0, 58, 0, 0, 58, 0, 0, 0, 0, 72629628, 7928237, 24671789, 0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 52, 50, 50, 0, 50, 50, 52, 0]
theorem block143 : ∀ u ∈ List.range 32, !valid5 (4576+u) || check (word5 (4576+u)) cert143[u]! = true := by decide +kernel

theorem portion17 (h : Nat) (lo : 4352≤h) (hi : h<4608) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t140 : h<4480
  ·
    by_cases t138 : h<4416
    ·
      by_cases t137 : h<4384
      ·
        have H := block136 (h-4352) (List.mem_range.mpr (by omega))
        have E : 4352+(h-4352)=h := by omega
        rw [E,valid] at H
        exact ⟨cert136[h-4352]!,by simpa using H⟩
      ·
        have H := block137 (h-4384) (List.mem_range.mpr (by omega))
        have E : 4384+(h-4384)=h := by omega
        rw [E,valid] at H
        exact ⟨cert137[h-4384]!,by simpa using H⟩
    ·
      by_cases t139 : h<4448
      ·
        have H := block138 (h-4416) (List.mem_range.mpr (by omega))
        have E : 4416+(h-4416)=h := by omega
        rw [E,valid] at H
        exact ⟨cert138[h-4416]!,by simpa using H⟩
      ·
        have H := block139 (h-4448) (List.mem_range.mpr (by omega))
        have E : 4448+(h-4448)=h := by omega
        rw [E,valid] at H
        exact ⟨cert139[h-4448]!,by simpa using H⟩
  ·
    by_cases t142 : h<4544
    ·
      by_cases t141 : h<4512
      ·
        have H := block140 (h-4480) (List.mem_range.mpr (by omega))
        have E : 4480+(h-4480)=h := by omega
        rw [E,valid] at H
        exact ⟨cert140[h-4480]!,by simpa using H⟩
      ·
        have H := block141 (h-4512) (List.mem_range.mpr (by omega))
        have E : 4512+(h-4512)=h := by omega
        rw [E,valid] at H
        exact ⟨cert141[h-4512]!,by simpa using H⟩
    ·
      by_cases t143 : h<4576
      ·
        have H := block142 (h-4544) (List.mem_range.mpr (by omega))
        have E : 4544+(h-4544)=h := by omega
        rw [E,valid] at H
        exact ⟨cert142[h-4544]!,by simpa using H⟩
      ·
        have H := block143 (h-4576) (List.mem_range.mpr (by omega))
        have E : 4576+(h-4576)=h := by omega
        rw [E,valid] at H
        exact ⟨cert143[h-4576]!,by simpa using H⟩
end BikovEight
