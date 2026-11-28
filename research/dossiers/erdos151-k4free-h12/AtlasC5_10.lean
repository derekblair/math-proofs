import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert80 : Array Nat := #[53, 86, 84, 54, 54, 0, 84, 54, 84, 85, 54, 0, 0, 84, 52, 52, 52, 0, 52, 71483248, 0, 52, 52, 42417961, 0, 84, 85, 86, 84, 0, 84, 85]
theorem block80 : ∀ u ∈ List.range 32, !valid5 (2560+u) || check (word5 (2560+u)) cert80[u]! = true := by decide +kernel
def cert81 : Array Nat := #[0, 0, 86, 84, 52, 52, 52, 42385200, 52, 0, 71516009, 52, 52, 0, 0, 53, 0, 53, 0, 53, 71483249, 0, 0, 53, 71483250, 0, 84, 0, 86, 84, 0, 84]
theorem block81 : ∀ u ∈ List.range 32, !valid5 (2592+u) || check (word5 (2592+u)) cert81[u]! = true := by decide +kernel
def cert82 : Array Nat := #[0, 0, 0, 86, 84, 84, 85, 0, 84, 0, 84, 85, 0, 0, 0, 84, 54, 54, 0, 42385201, 54, 0, 42385202, 54, 0, 0, 0, 52, 52, 52, 0, 52]
theorem block82 : ∀ u ∈ List.range 32, !valid5 (2624+u) || check (word5 (2624+u)) cert82[u]! = true := by decide +kernel
def cert83 : Array Nat := #[0, 0, 52, 52, 0, 0, 37, 42, 37, 41, 37, 37, 42, 50, 37, 37, 41, 37, 106, 37, 41, 37, 37, 106, 114, 37, 37, 41, 42, 42, 101, 42]
theorem block83 : ∀ u ∈ List.range 32, !valid5 (2656+u) || check (word5 (2656+u)) cert83[u]! = true := by decide +kernel
def cert84 : Array Nat := #[50, 42, 42, 50, 101, 101, 42, 37, 52, 37, 105, 37, 37, 106, 52, 37, 37, 105, 41, 42, 41, 41, 101, 41, 42, 114, 101, 41, 41, 50, 50, 52]
theorem block84 : ∀ u ∈ List.range 32, !valid5 (2688+u) || check (word5 (2688+u)) cert84[u]! = true := by decide +kernel
def cert85 : Array Nat := #[50, 50, 101, 50, 50, 52, 101, 105, 37, 106, 37, 106, 37, 37, 106, 114, 37, 37, 106, 41, 114, 41, 41, 114, 41, 114, 114, 116, 41, 41, 42, 42]
theorem block85 : ∀ u ∈ List.range 32, !valid5 (2720+u) || check (word5 (2720+u)) cert85[u]! = true := by decide +kernel
def cert86 : Array Nat := #[101, 42, 101, 42, 42, 116, 101, 101, 42, 50, 50, 101, 50, 50, 101, 50, 50, 101, 101, 105, 52, 52, 52, 105, 52, 105, 106, 52, 52, 105, 105, 37]
theorem block86 : ∀ u ∈ List.range 32, !valid5 (2752+u) || check (word5 (2752+u)) cert86[u]! = true := by decide +kernel
def cert87 : Array Nat := #[0, 37, 41, 37, 37, 0, 0, 37, 37, 41, 37, 0, 37, 41, 37, 37, 0, 0, 37, 37, 41, 43, 0, 101, 43, 101, 43, 0, 0, 101, 101, 43]
theorem block87 : ∀ u ∈ List.range 32, !valid5 (2784+u) || check (word5 (2784+u)) cert87[u]! = true := by decide +kernel

theorem portion10 (h : Nat) (lo : 2560≤h) (hi : h<2816) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t84 : h<2688
  ·
    by_cases t82 : h<2624
    ·
      by_cases t81 : h<2592
      ·
        have H := block80 (h-2560) (List.mem_range.mpr (by omega))
        have E : 2560+(h-2560)=h := by omega
        rw [E,valid] at H
        exact ⟨cert80[h-2560]!,by simpa using H⟩
      ·
        have H := block81 (h-2592) (List.mem_range.mpr (by omega))
        have E : 2592+(h-2592)=h := by omega
        rw [E,valid] at H
        exact ⟨cert81[h-2592]!,by simpa using H⟩
    ·
      by_cases t83 : h<2656
      ·
        have H := block82 (h-2624) (List.mem_range.mpr (by omega))
        have E : 2624+(h-2624)=h := by omega
        rw [E,valid] at H
        exact ⟨cert82[h-2624]!,by simpa using H⟩
      ·
        have H := block83 (h-2656) (List.mem_range.mpr (by omega))
        have E : 2656+(h-2656)=h := by omega
        rw [E,valid] at H
        exact ⟨cert83[h-2656]!,by simpa using H⟩
  ·
    by_cases t86 : h<2752
    ·
      by_cases t85 : h<2720
      ·
        have H := block84 (h-2688) (List.mem_range.mpr (by omega))
        have E : 2688+(h-2688)=h := by omega
        rw [E,valid] at H
        exact ⟨cert84[h-2688]!,by simpa using H⟩
      ·
        have H := block85 (h-2720) (List.mem_range.mpr (by omega))
        have E : 2720+(h-2720)=h := by omega
        rw [E,valid] at H
        exact ⟨cert85[h-2720]!,by simpa using H⟩
    ·
      by_cases t87 : h<2784
      ·
        have H := block86 (h-2752) (List.mem_range.mpr (by omega))
        have E : 2752+(h-2752)=h := by omega
        rw [E,valid] at H
        exact ⟨cert86[h-2752]!,by simpa using H⟩
      ·
        have H := block87 (h-2784) (List.mem_range.mpr (by omega))
        have E : 2784+(h-2784)=h := by omega
        rw [E,valid] at H
        exact ⟨cert87[h-2784]!,by simpa using H⟩
end BikovEight
