import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert208 : Array Nat := #[69, 74, 69, 73, 82, 69, 73, 74, 82, 84, 74, 0, 74, 84, 74, 82, 0, 0, 74, 82, 84, 69, 69, 0, 69, 73, 84, 69, 73, 0, 0, 84]
theorem block208 : ∀ u ∈ List.range 32, !valid5 (6656+u) || check (word5 (6656+u)) cert208[u]! = true := by decide +kernel
def cert209 : Array Nat := #[73, 73, 74, 0, 73, 82, 0, 73, 74, 82, 0, 69, 69, 82, 69, 0, 82, 69, 0, 0, 82, 84, 69, 69, 74, 69, 73, 0, 69, 73, 74, 0]
theorem block209 : ∀ u ∈ List.range 32, !valid5 (6688+u) || check (word5 (6688+u)) cert209[u]! = true := by decide +kernel
def cert210 : Array Nat := #[0, 74, 0, 74, 0, 74, 82, 0, 0, 74, 82, 0, 82, 0, 82, 84, 0, 82, 0, 0, 0, 82, 84, 69, 69, 0, 69, 0, 84, 69, 0, 0]
theorem block210 : ∀ u ∈ List.range 32, !valid5 (6720+u) || check (word5 (6720+u)) cert210[u]! = true := by decide +kernel
def cert211 : Array Nat := #[0, 84, 69, 69, 0, 69, 73, 0, 69, 73, 0, 0, 0, 73, 73, 74, 0, 73, 0, 0, 73, 74, 0, 0, 69, 69, 75, 69, 73, 85, 69, 73]
theorem block211 : ∀ u ∈ List.range 32, !valid5 (6752+u) || check (word5 (6752+u)) cert211[u]! = true := by decide +kernel
def cert212 : Array Nat := #[75, 26807292, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 0, 69, 73, 85, 69, 73, 0, 0, 85, 73, 73, 75, 0, 73, 71513211, 0]
theorem block212 : ∀ u ∈ List.range 32, !valid5 (6784+u) || check (word5 (6784+u)) cert212[u]! = true := by decide +kernel
def cert213 : Array Nat := #[73, 75, 34993205, 0, 69, 69, 23276155, 69, 0, 85, 69, 0, 0, 51738997, 85, 69, 69, 75, 69, 73, 0, 69, 73, 75, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block213 : ∀ u ∈ List.range 32, !valid5 (6816+u) || check (word5 (6816+u)) cert213[u]! = true := by decide +kernel
def cert214 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 0, 69, 0, 85, 69, 0, 0, 0, 85, 69, 69, 0, 69, 73]
theorem block214 : ∀ u ∈ List.range 32, !valid5 (6848+u) || check (word5 (6848+u)) cert214[u]! = true := by decide +kernel
def cert215 : Array Nat := #[0, 69, 73, 0, 0, 0, 73, 73, 75, 0, 73, 0, 0, 73, 75, 0, 0, 74, 75, 74, 86, 74, 82, 35232828, 75, 74, 82, 86, 74, 0, 74, 86]
theorem block215 : ∀ u ∈ List.range 32, !valid5 (6880+u) || check (word5 (6880+u)) cert215[u]! = true := by decide +kernel

theorem portion26 (h : Nat) (lo : 6656≤h) (hi : h<6912) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t212 : h<6784
  ·
    by_cases t210 : h<6720
    ·
      by_cases t209 : h<6688
      ·
        have H := block208 (h-6656) (List.mem_range.mpr (by omega))
        have E : 6656+(h-6656)=h := by omega
        rw [E,valid] at H
        exact ⟨cert208[h-6656]!,by simpa using H⟩
      ·
        have H := block209 (h-6688) (List.mem_range.mpr (by omega))
        have E : 6688+(h-6688)=h := by omega
        rw [E,valid] at H
        exact ⟨cert209[h-6688]!,by simpa using H⟩
    ·
      by_cases t211 : h<6752
      ·
        have H := block210 (h-6720) (List.mem_range.mpr (by omega))
        have E : 6720+(h-6720)=h := by omega
        rw [E,valid] at H
        exact ⟨cert210[h-6720]!,by simpa using H⟩
      ·
        have H := block211 (h-6752) (List.mem_range.mpr (by omega))
        have E : 6752+(h-6752)=h := by omega
        rw [E,valid] at H
        exact ⟨cert211[h-6752]!,by simpa using H⟩
  ·
    by_cases t214 : h<6848
    ·
      by_cases t213 : h<6816
      ·
        have H := block212 (h-6784) (List.mem_range.mpr (by omega))
        have E : 6784+(h-6784)=h := by omega
        rw [E,valid] at H
        exact ⟨cert212[h-6784]!,by simpa using H⟩
      ·
        have H := block213 (h-6816) (List.mem_range.mpr (by omega))
        have E : 6816+(h-6816)=h := by omega
        rw [E,valid] at H
        exact ⟨cert213[h-6816]!,by simpa using H⟩
    ·
      by_cases t215 : h<6880
      ·
        have H := block214 (h-6848) (List.mem_range.mpr (by omega))
        have E : 6848+(h-6848)=h := by omega
        rw [E,valid] at H
        exact ⟨cert214[h-6848]!,by simpa using H⟩
      ·
        have H := block215 (h-6880) (List.mem_range.mpr (by omega))
        have E : 6880+(h-6880)=h := by omega
        rw [E,valid] at H
        exact ⟨cert215[h-6880]!,by simpa using H⟩
end BikovEight
