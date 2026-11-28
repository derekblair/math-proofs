import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert120 : Array Nat := #[58, 0, 58, 53652793, 0, 58, 53652794, 0, 0, 0, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 54, 54, 0, 42384697, 54, 0, 42384698, 54, 0, 0, 0]
theorem block120 : ∀ u ∈ List.range 32, !valid5 (3840+u) || check (word5 (3840+u)) cert120[u]! = true := by decide +kernel
def cert121 : Array Nat := #[52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 53, 116, 53, 0, 53, 0, 0, 116, 53, 0, 0, 54, 54, 116, 0, 54, 0, 0, 54, 116, 0]
theorem block121 : ∀ u ∈ List.range 32, !valid5 (3872+u) || check (word5 (3872+u)) cert121[u]! = true := by decide +kernel
def cert122 : Array Nat := #[0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 116, 116, 116, 0, 116, 0, 0, 116, 116, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52]
theorem block122 : ∀ u ∈ List.range 32, !valid5 (3904+u) || check (word5 (3904+u)) cert122[u]! = true := by decide +kernel
def cert123 : Array Nat := #[0, 0, 53, 5414393, 53, 0, 53, 0, 0, 5414394, 53, 0, 0, 116, 116, 116, 0, 116, 0, 0, 116, 116, 0, 0, 116, 116, 116, 0, 116, 0, 0, 116]
theorem block123 : ∀ u ∈ List.range 32, !valid5 (3936+u) || check (word5 (3936+u)) cert123[u]! = true := by decide +kernel
def cert124 : Array Nat := #[116, 0, 0, 54, 54, 25857529, 0, 54, 0, 0, 54, 25857530, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 37, 42, 37, 41, 37, 37, 42]
theorem block124 : ∀ u ∈ List.range 32, !valid5 (3968+u) || check (word5 (3968+u)) cert124[u]! = true := by decide +kernel
def cert125 : Array Nat := #[50, 37, 37, 41, 37, 0, 37, 41, 37, 37, 0, 0, 37, 37, 41, 42, 42, 0, 42, 50, 42, 42, 50, 0, 0, 42, 37, 52, 37, 0, 37, 37]
theorem block125 : ∀ u ∈ List.range 32, !valid5 (4000+u) || check (word5 (4000+u)) cert125[u]! = true := by decide +kernel
def cert126 : Array Nat := #[0, 52, 37, 37, 0, 41, 42, 41, 41, 0, 41, 42, 0, 0, 41, 41, 50, 50, 52, 50, 50, 0, 50, 50, 52, 0, 0, 37, 0, 37, 0, 37]
theorem block126 : ∀ u ∈ List.range 32, !valid5 (4032+u) || check (word5 (4032+u)) cert126[u]! = true := by decide +kernel
def cert127 : Array Nat := #[37, 0, 0, 37, 37, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 50, 50, 0, 50]
theorem block127 : ∀ u ∈ List.range 32, !valid5 (4064+u) || check (word5 (4064+u)) cert127[u]! = true := by decide +kernel

theorem portion15 (h : Nat) (lo : 3840≤h) (hi : h<4096) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t124 : h<3968
  ·
    by_cases t122 : h<3904
    ·
      by_cases t121 : h<3872
      ·
        have H := block120 (h-3840) (List.mem_range.mpr (by omega))
        have E : 3840+(h-3840)=h := by omega
        rw [E,valid] at H
        exact ⟨cert120[h-3840]!,by simpa using H⟩
      ·
        have H := block121 (h-3872) (List.mem_range.mpr (by omega))
        have E : 3872+(h-3872)=h := by omega
        rw [E,valid] at H
        exact ⟨cert121[h-3872]!,by simpa using H⟩
    ·
      by_cases t123 : h<3936
      ·
        have H := block122 (h-3904) (List.mem_range.mpr (by omega))
        have E : 3904+(h-3904)=h := by omega
        rw [E,valid] at H
        exact ⟨cert122[h-3904]!,by simpa using H⟩
      ·
        have H := block123 (h-3936) (List.mem_range.mpr (by omega))
        have E : 3936+(h-3936)=h := by omega
        rw [E,valid] at H
        exact ⟨cert123[h-3936]!,by simpa using H⟩
  ·
    by_cases t126 : h<4032
    ·
      by_cases t125 : h<4000
      ·
        have H := block124 (h-3968) (List.mem_range.mpr (by omega))
        have E : 3968+(h-3968)=h := by omega
        rw [E,valid] at H
        exact ⟨cert124[h-3968]!,by simpa using H⟩
      ·
        have H := block125 (h-4000) (List.mem_range.mpr (by omega))
        have E : 4000+(h-4000)=h := by omega
        rw [E,valid] at H
        exact ⟨cert125[h-4000]!,by simpa using H⟩
    ·
      by_cases t127 : h<4064
      ·
        have H := block126 (h-4032) (List.mem_range.mpr (by omega))
        have E : 4032+(h-4032)=h := by omega
        rw [E,valid] at H
        exact ⟨cert126[h-4032]!,by simpa using H⟩
      ·
        have H := block127 (h-4064) (List.mem_range.mpr (by omega))
        have E : 4064+(h-4064)=h := by omega
        rw [E,valid] at H
        exact ⟨cert127[h-4064]!,by simpa using H⟩
end BikovEight
