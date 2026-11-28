import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert192 : Array Nat := #[69, 51071866, 101, 101, 85, 69, 69, 101, 69, 77, 101, 69, 77, 101, 101, 71515002, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 75, 77, 73]
theorem block192 : ∀ u ∈ List.range 32, !valid5 (6144+u) || check (word5 (6144+u)) cert192[u]! = true := by decide +kernel
def cert193 : Array Nat := #[105, 77, 73, 75, 105, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 105, 77, 73, 105, 77, 73, 23276601, 105, 105, 73, 73, 75, 105]
theorem block193 : ∀ u ∈ List.range 32, !valid5 (6176+u) || check (word5 (6176+u)) cert193[u]! = true := by decide +kernel
def cert194 : Array Nat := #[73, 105, 34544697, 73, 75, 105, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 75, 77, 73, 105, 77, 73, 75, 105, 105, 0, 0, 0]
theorem block194 : ∀ u ∈ List.range 32, !valid5 (6208+u) || check (word5 (6208+u)) cert194[u]! = true := by decide +kernel
def cert195 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73]
theorem block195 : ∀ u ∈ List.range 32, !valid5 (6240+u) || check (word5 (6240+u)) cert195[u]! = true := by decide +kernel
def cert196 : Array Nat := #[105, 77, 73, 105, 77, 73, 23276602, 105, 105, 73, 73, 75, 105, 73, 105, 34544698, 73, 75, 105, 105, 74, 75, 74, 106, 74, 90, 106, 75, 74, 90, 106, 74]
theorem block196 : ∀ u ∈ List.range 32, !valid5 (6272+u) || check (word5 (6272+u)) cert196[u]! = true := by decide +kernel
def cert197 : Array Nat := #[106, 74, 106, 74, 90, 106, 6769593, 74, 90, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 75, 74, 106, 74, 90, 106, 75, 74, 90, 106]
theorem block197 : ∀ u ∈ List.range 32, !valid5 (6304+u) || check (word5 (6304+u)) cert197[u]! = true := by decide +kernel
def cert198 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 75, 74, 106, 74, 106, 106, 75, 74, 70192057, 106, 74, 106, 74, 106, 74, 90, 106, 6769594, 74, 90]
theorem block198 : ∀ u ∈ List.range 32, !valid5 (6336+u) || check (word5 (6336+u)) cert198[u]! = true := by decide +kernel
def cert199 : Array Nat := #[106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block199 : ∀ u ∈ List.range 32, !valid5 (6368+u) || check (word5 (6368+u)) cert199[u]! = true := by decide +kernel

theorem portion24 (h : Nat) (lo : 6144≤h) (hi : h<6400) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t196 : h<6272
  ·
    by_cases t194 : h<6208
    ·
      by_cases t193 : h<6176
      ·
        have H := block192 (h-6144) (List.mem_range.mpr (by omega))
        have E : 6144+(h-6144)=h := by omega
        rw [E,valid] at H
        exact ⟨cert192[h-6144]!,by simpa using H⟩
      ·
        have H := block193 (h-6176) (List.mem_range.mpr (by omega))
        have E : 6176+(h-6176)=h := by omega
        rw [E,valid] at H
        exact ⟨cert193[h-6176]!,by simpa using H⟩
    ·
      by_cases t195 : h<6240
      ·
        have H := block194 (h-6208) (List.mem_range.mpr (by omega))
        have E : 6208+(h-6208)=h := by omega
        rw [E,valid] at H
        exact ⟨cert194[h-6208]!,by simpa using H⟩
      ·
        have H := block195 (h-6240) (List.mem_range.mpr (by omega))
        have E : 6240+(h-6240)=h := by omega
        rw [E,valid] at H
        exact ⟨cert195[h-6240]!,by simpa using H⟩
  ·
    by_cases t198 : h<6336
    ·
      by_cases t197 : h<6304
      ·
        have H := block196 (h-6272) (List.mem_range.mpr (by omega))
        have E : 6272+(h-6272)=h := by omega
        rw [E,valid] at H
        exact ⟨cert196[h-6272]!,by simpa using H⟩
      ·
        have H := block197 (h-6304) (List.mem_range.mpr (by omega))
        have E : 6304+(h-6304)=h := by omega
        rw [E,valid] at H
        exact ⟨cert197[h-6304]!,by simpa using H⟩
    ·
      by_cases t199 : h<6368
      ·
        have H := block198 (h-6336) (List.mem_range.mpr (by omega))
        have E : 6336+(h-6336)=h := by omega
        rw [E,valid] at H
        exact ⟨cert198[h-6336]!,by simpa using H⟩
      ·
        have H := block199 (h-6368) (List.mem_range.mpr (by omega))
        have E : 6368+(h-6368)=h := by omega
        rw [E,valid] at H
        exact ⟨cert199[h-6368]!,by simpa using H⟩
end BikovEight
