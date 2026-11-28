import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert88 : Array Nat := #[37, 0, 37, 105, 37, 37, 0, 0, 37, 37, 105, 41, 0, 41, 41, 101, 41, 0, 0, 101, 41, 41, 53, 0, 53, 105, 53, 101, 0, 0, 53, 101]
theorem block88 : ∀ u ∈ List.range 32, !valid5 (2816+u) || check (word5 (2816+u)) cert88[u]! = true := by decide +kernel
def cert89 : Array Nat := #[105, 37, 0, 37, 34512440, 37, 37, 0, 0, 37, 37, 5479913, 41, 0, 41, 41, 51039608, 41, 0, 0, 6802857, 41, 41, 43, 0, 101, 43, 101, 43, 0, 0, 101]
theorem block89 : ∀ u ∈ List.range 32, !valid5 (2848+u) || check (word5 (2848+u)) cert89[u]! = true := by decide +kernel
def cert90 : Array Nat := #[101, 43, 101, 0, 101, 105, 101, 101, 0, 0, 101, 101, 105, 53, 0, 53, 105, 53, 105, 0, 0, 53, 105, 105, 42, 42, 0, 42, 50, 42, 42, 50]
theorem block90 : ∀ u ∈ List.range 32, !valid5 (2880+u) || check (word5 (2880+u)) cert90[u]! = true := by decide +kernel
def cert91 : Array Nat := #[0, 0, 42, 43, 106, 0, 43, 114, 43, 106, 114, 0, 0, 43, 42, 42, 0, 42, 50, 42, 42, 50, 0, 0, 42, 54, 54, 0, 106, 54, 106, 106]
theorem block91 : ∀ u ∈ List.range 32, !valid5 (2912+u) || check (word5 (2912+u)) cert91[u]! = true := by decide +kernel
def cert92 : Array Nat := #[54, 0, 0, 106, 42, 42, 0, 42, 114, 42, 42, 114, 0, 0, 42, 50, 50, 0, 50, 50, 106, 50, 50, 0, 0, 106, 106, 106, 0, 106, 114, 106]
theorem block92 : ∀ u ∈ List.range 32, !valid5 (2944+u) || check (word5 (2944+u)) cert92[u]! = true := by decide +kernel
def cert93 : Array Nat := #[106, 114, 0, 0, 106, 43, 114, 0, 43, 114, 43, 114, 114, 0, 0, 43, 42, 42, 0, 42, 53652792, 42, 42, 23309865, 0, 0, 42, 50, 50, 0, 50, 50]
theorem block93 : ∀ u ∈ List.range 32, !valid5 (2976+u) || check (word5 (2976+u)) cert93[u]! = true := by decide +kernel
def cert94 : Array Nat := #[70159800, 50, 50, 0, 0, 25923049, 54, 54, 0, 106, 54, 106, 106, 54, 0, 0, 106, 37, 52, 37, 0, 37, 37, 0, 52, 37, 37, 0, 37, 116, 37, 0]
theorem block94 : ∀ u ∈ List.range 32, !valid5 (3008+u) || check (word5 (3008+u)) cert94[u]! = true := by decide +kernel
def cert95 : Array Nat := #[37, 37, 0, 116, 37, 37, 0, 54, 54, 101, 0, 54, 101, 0, 54, 101, 101, 0, 37, 52, 37, 0, 37, 37, 0, 52, 37, 37, 0, 45, 116, 45]
theorem block95 : ∀ u ∈ List.range 32, !valid5 (3040+u) || check (word5 (3040+u)) cert95[u]! = true := by decide +kernel

theorem portion11 (h : Nat) (lo : 2816≤h) (hi : h<3072) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t92 : h<2944
  ·
    by_cases t90 : h<2880
    ·
      by_cases t89 : h<2848
      ·
        have H := block88 (h-2816) (List.mem_range.mpr (by omega))
        have E : 2816+(h-2816)=h := by omega
        rw [E,valid] at H
        exact ⟨cert88[h-2816]!,by simpa using H⟩
      ·
        have H := block89 (h-2848) (List.mem_range.mpr (by omega))
        have E : 2848+(h-2848)=h := by omega
        rw [E,valid] at H
        exact ⟨cert89[h-2848]!,by simpa using H⟩
    ·
      by_cases t91 : h<2912
      ·
        have H := block90 (h-2880) (List.mem_range.mpr (by omega))
        have E : 2880+(h-2880)=h := by omega
        rw [E,valid] at H
        exact ⟨cert90[h-2880]!,by simpa using H⟩
      ·
        have H := block91 (h-2912) (List.mem_range.mpr (by omega))
        have E : 2912+(h-2912)=h := by omega
        rw [E,valid] at H
        exact ⟨cert91[h-2912]!,by simpa using H⟩
  ·
    by_cases t94 : h<3008
    ·
      by_cases t93 : h<2976
      ·
        have H := block92 (h-2944) (List.mem_range.mpr (by omega))
        have E : 2944+(h-2944)=h := by omega
        rw [E,valid] at H
        exact ⟨cert92[h-2944]!,by simpa using H⟩
      ·
        have H := block93 (h-2976) (List.mem_range.mpr (by omega))
        have E : 2976+(h-2976)=h := by omega
        rw [E,valid] at H
        exact ⟨cert93[h-2976]!,by simpa using H⟩
    ·
      by_cases t95 : h<3040
      ·
        have H := block94 (h-3008) (List.mem_range.mpr (by omega))
        have E : 3008+(h-3008)=h := by omega
        rw [E,valid] at H
        exact ⟨cert94[h-3008]!,by simpa using H⟩
      ·
        have H := block95 (h-3040) (List.mem_range.mpr (by omega))
        have E : 3040+(h-3040)=h := by omega
        rw [E,valid] at H
        exact ⟨cert95[h-3040]!,by simpa using H⟩
end BikovEight
