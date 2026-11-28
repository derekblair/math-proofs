import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert224 : Array Nat := #[73, 0, 0, 24409653, 73, 73, 74, 0, 73, 90, 0, 73, 74, 90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 74, 77, 73, 0]
theorem block224 : ∀ u ∈ List.range 32, !valid5 (7168+u) || check (word5 (7168+u)) cert224[u]! = true := by decide +kernel
def cert225 : Array Nat := #[77, 73, 74, 0, 0, 74, 0, 74, 0, 74, 90, 0, 0, 74, 90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block225 : ∀ u ∈ List.range 32, !valid5 (7200+u) || check (word5 (7200+u)) cert225[u]! = true := by decide +kernel
def cert226 : Array Nat := #[0, 0, 0, 0, 0, 0, 73, 73, 0, 77, 73, 0, 77, 73, 0, 0, 0, 73, 73, 74, 0, 73, 0, 0, 73, 74, 0, 0, 82, 85, 82, 84]
theorem block226 : ∀ u ∈ List.range 32, !valid5 (7232+u) || check (word5 (7232+u)) cert226[u]! = true := by decide +kernel
def cert227 : Array Nat := #[90, 82, 85, 7916476, 90, 82, 84, 82, 0, 82, 84, 90, 82, 0, 0, 90, 82, 84, 84, 85, 0, 84, 53682811, 84, 85, 26571253, 0, 0, 84, 82, 5445755, 82]
theorem block227 : ∀ u ∈ List.range 32, !valid5 (7264+u) || check (word5 (7264+u)) cert227[u]! = true := by decide +kernel
def cert228 : Array Nat := #[0, 90, 82, 0, 43317045, 90, 82, 0, 82, 85, 82, 84, 0, 82, 85, 0, 0, 82, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 0]
theorem block228 : ∀ u ∈ List.range 32, !valid5 (7296+u) || check (word5 (7296+u)) cert228[u]! = true := by decide +kernel
def cert229 : Array Nat := #[82, 0, 90, 82, 0, 0, 90, 82, 0, 82, 0, 82, 84, 0, 82, 0, 0, 0, 82, 84, 84, 85, 0, 84, 0, 84, 85, 0, 0, 0, 84, 0]
theorem block229 : ∀ u ∈ List.range 32, !valid5 (7328+u) || check (word5 (7328+u)) cert229[u]! = true := by decide +kernel
def cert230 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 34993204, 69, 77, 85, 69, 77, 11166717, 44164157, 85]
theorem block230 : ∀ u ∈ List.range 32, !valid5 (7360+u) || check (word5 (7360+u)) cert230[u]! = true := by decide +kernel
def cert231 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 0, 69, 77, 85, 69, 77, 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block231 : ∀ u ∈ List.range 32, !valid5 (7392+u) || check (word5 (7392+u)) cert231[u]! = true := by decide +kernel

theorem portion28 (h : Nat) (lo : 7168≤h) (hi : h<7424) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t228 : h<7296
  ·
    by_cases t226 : h<7232
    ·
      by_cases t225 : h<7200
      ·
        have H := block224 (h-7168) (List.mem_range.mpr (by omega))
        have E : 7168+(h-7168)=h := by omega
        rw [E,valid] at H
        exact ⟨cert224[h-7168]!,by simpa using H⟩
      ·
        have H := block225 (h-7200) (List.mem_range.mpr (by omega))
        have E : 7200+(h-7200)=h := by omega
        rw [E,valid] at H
        exact ⟨cert225[h-7200]!,by simpa using H⟩
    ·
      by_cases t227 : h<7264
      ·
        have H := block226 (h-7232) (List.mem_range.mpr (by omega))
        have E : 7232+(h-7232)=h := by omega
        rw [E,valid] at H
        exact ⟨cert226[h-7232]!,by simpa using H⟩
      ·
        have H := block227 (h-7264) (List.mem_range.mpr (by omega))
        have E : 7264+(h-7264)=h := by omega
        rw [E,valid] at H
        exact ⟨cert227[h-7264]!,by simpa using H⟩
  ·
    by_cases t230 : h<7360
    ·
      by_cases t229 : h<7328
      ·
        have H := block228 (h-7296) (List.mem_range.mpr (by omega))
        have E : 7296+(h-7296)=h := by omega
        rw [E,valid] at H
        exact ⟨cert228[h-7296]!,by simpa using H⟩
      ·
        have H := block229 (h-7328) (List.mem_range.mpr (by omega))
        have E : 7328+(h-7328)=h := by omega
        rw [E,valid] at H
        exact ⟨cert229[h-7328]!,by simpa using H⟩
    ·
      by_cases t231 : h<7392
      ·
        have H := block230 (h-7360) (List.mem_range.mpr (by omega))
        have E : 7360+(h-7360)=h := by omega
        rw [E,valid] at H
        exact ⟨cert230[h-7360]!,by simpa using H⟩
      ·
        have H := block231 (h-7392) (List.mem_range.mpr (by omega))
        have E : 7392+(h-7392)=h := by omega
        rw [E,valid] at H
        exact ⟨cert231[h-7392]!,by simpa using H⟩
end BikovEight
