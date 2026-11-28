import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert200 : Array Nat := #[0, 0, 74, 75, 74, 106, 74, 106, 106, 75, 74, 70192058, 106, 82, 114, 82, 86, 90, 82, 114, 114, 90, 82, 86, 82, 114, 82, 86, 90, 82, 114, 114]
theorem block200 : ∀ u ∈ List.range 32, !valid5 (6400+u) || check (word5 (6400+u)) cert200[u]! = true := by decide +kernel
def cert201 : Array Nat := #[90, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 114, 82, 114, 90, 82, 114, 114, 90, 82, 42416953, 82, 114, 82, 86, 114, 82, 114]
theorem block201 : ∀ u ∈ List.range 32, !valid5 (6432+u) || check (word5 (6432+u)) cert201[u]! = true := by decide +kernel
def cert202 : Array Nat := #[114, 53685049, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 114, 82, 114, 90, 82, 114, 114, 90, 82, 42416954, 82, 114, 82, 86, 114, 82]
theorem block202 : ∀ u ∈ List.range 32, !valid5 (6464+u) || check (word5 (6464+u)) cert202[u]! = true := by decide +kernel
def cert203 : Array Nat := #[114, 114, 53685050, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block203 : ∀ u ∈ List.range 32, !valid5 (6496+u) || check (word5 (6496+u)) cert203[u]! = true := by decide +kernel
def cert204 : Array Nat := #[0, 0, 0, 0, 0, 0, 84, 85, 86, 84, 116, 84, 85, 116, 116, 86, 84, 84, 116, 86, 84, 116, 84, 5446649, 116, 116, 86, 84, 84, 85, 116, 84]
theorem block204 : ∀ u ∈ List.range 32, !valid5 (6528+u) || check (word5 (6528+u)) cert204[u]! = true := by decide +kernel
def cert205 : Array Nat := #[116, 84, 85, 116, 116, 25889785, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 85, 86, 84, 116, 84, 85, 116, 116, 86, 84, 0, 0, 0]
theorem block205 : ∀ u ∈ List.range 32, !valid5 (6560+u) || check (word5 (6560+u)) cert205[u]! = true := by decide +kernel
def cert206 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 116, 86, 84, 116, 84, 5446650, 116, 116, 86, 84, 84, 85]
theorem block206 : ∀ u ∈ List.range 32, !valid5 (6592+u) || check (word5 (6592+u)) cert206[u]! = true := by decide +kernel
def cert207 : Array Nat := #[116, 84, 116, 84, 85, 116, 116, 25889786, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69]
theorem block207 : ∀ u ∈ List.range 32, !valid5 (6624+u) || check (word5 (6624+u)) cert207[u]! = true := by decide +kernel

theorem portion25 (h : Nat) (lo : 6400≤h) (hi : h<6656) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t204 : h<6528
  ·
    by_cases t202 : h<6464
    ·
      by_cases t201 : h<6432
      ·
        have H := block200 (h-6400) (List.mem_range.mpr (by omega))
        have E : 6400+(h-6400)=h := by omega
        rw [E,valid] at H
        exact ⟨cert200[h-6400]!,by simpa using H⟩
      ·
        have H := block201 (h-6432) (List.mem_range.mpr (by omega))
        have E : 6432+(h-6432)=h := by omega
        rw [E,valid] at H
        exact ⟨cert201[h-6432]!,by simpa using H⟩
    ·
      by_cases t203 : h<6496
      ·
        have H := block202 (h-6464) (List.mem_range.mpr (by omega))
        have E : 6464+(h-6464)=h := by omega
        rw [E,valid] at H
        exact ⟨cert202[h-6464]!,by simpa using H⟩
      ·
        have H := block203 (h-6496) (List.mem_range.mpr (by omega))
        have E : 6496+(h-6496)=h := by omega
        rw [E,valid] at H
        exact ⟨cert203[h-6496]!,by simpa using H⟩
  ·
    by_cases t206 : h<6592
    ·
      by_cases t205 : h<6560
      ·
        have H := block204 (h-6528) (List.mem_range.mpr (by omega))
        have E : 6528+(h-6528)=h := by omega
        rw [E,valid] at H
        exact ⟨cert204[h-6528]!,by simpa using H⟩
      ·
        have H := block205 (h-6560) (List.mem_range.mpr (by omega))
        have E : 6560+(h-6560)=h := by omega
        rw [E,valid] at H
        exact ⟨cert205[h-6560]!,by simpa using H⟩
    ·
      by_cases t207 : h<6624
      ·
        have H := block206 (h-6592) (List.mem_range.mpr (by omega))
        have E : 6592+(h-6592)=h := by omega
        rw [E,valid] at H
        exact ⟨cert206[h-6592]!,by simpa using H⟩
      ·
        have H := block207 (h-6624) (List.mem_range.mpr (by omega))
        have E : 6624+(h-6624)=h := by omega
        rw [E,valid] at H
        exact ⟨cert207[h-6624]!,by simpa using H⟩
end BikovEight
