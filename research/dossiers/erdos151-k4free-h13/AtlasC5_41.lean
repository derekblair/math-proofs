import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert328 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block328 : ∀ u ∈ List.range 32, !valid5 (10496+u) || check (word5 (10496+u)) cert328[u]! = true := by decide +kernel
def cert329 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block329 : ∀ u ∈ List.range 32, !valid5 (10528+u) || check (word5 (10528+u)) cert329[u]! = true := by decide +kernel
def cert330 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block330 : ∀ u ∈ List.range 32, !valid5 (10560+u) || check (word5 (10560+u)) cert330[u]! = true := by decide +kernel
def cert331 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block331 : ∀ u ∈ List.range 32, !valid5 (10592+u) || check (word5 (10592+u)) cert331[u]! = true := by decide +kernel
def cert332 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block332 : ∀ u ∈ List.range 24, !valid5 (10624+u) || check (word5 (10624+u)) cert332[u]! = true := by decide +kernel

theorem portion41 (h : Nat) (lo : 10496≤h) (hi : h<10648) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t330 : h<10560
  ·
    by_cases t329 : h<10528
    ·
      have H := block328 (h-10496) (List.mem_range.mpr (by omega))
      have E : 10496+(h-10496)=h := by omega
      rw [E,valid] at H
      exact ⟨cert328[h-10496]!,by simpa using H⟩
    ·
      have H := block329 (h-10528) (List.mem_range.mpr (by omega))
      have E : 10528+(h-10528)=h := by omega
      rw [E,valid] at H
      exact ⟨cert329[h-10528]!,by simpa using H⟩
  ·
    by_cases t331 : h<10592
    ·
      have H := block330 (h-10560) (List.mem_range.mpr (by omega))
      have E : 10560+(h-10560)=h := by omega
      rw [E,valid] at H
      exact ⟨cert330[h-10560]!,by simpa using H⟩
    ·
      by_cases t332 : h<10624
      ·
        have H := block331 (h-10592) (List.mem_range.mpr (by omega))
        have E : 10592+(h-10592)=h := by omega
        rw [E,valid] at H
        exact ⟨cert331[h-10592]!,by simpa using H⟩
      ·
        have H := block332 (h-10624) (List.mem_range.mpr (by omega))
        have E : 10624+(h-10624)=h := by omega
        rw [E,valid] at H
        exact ⟨cert332[h-10624]!,by simpa using H⟩
end BikovEight
