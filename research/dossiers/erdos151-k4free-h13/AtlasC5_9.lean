import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert72 : Array Nat := #[42, 42, 75, 74, 90, 42, 43, 0, 74, 43, 74, 43, 0, 0, 74, 90, 43, 42, 42, 0, 42, 53653296, 42, 42, 23277609, 0, 0, 42, 74, 75, 74, 0]
theorem block72 : ∀ u ∈ List.range 32, !valid5 (2304+u) || check (word5 (2304+u)) cert72[u]! = true := by decide +kernel
def cert73 : Array Nat := #[74, 90, 0, 75, 74, 90, 0, 42, 42, 23244848, 42, 0, 42, 42, 0, 0, 53686057, 42, 58, 58, 74, 58, 74, 0, 58, 75, 74, 0, 0, 74, 0, 74]
theorem block73 : ∀ u ∈ List.range 32, !valid5 (2336+u) || check (word5 (2336+u)) cert73[u]! = true := by decide +kernel
def cert74 : Array Nat := #[0, 74, 90, 0, 0, 74, 90, 0, 43, 0, 23244849, 43, 0, 43, 0, 0, 0, 23244850, 43, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 58, 58]
theorem block74 : ∀ u ∈ List.range 32, !valid5 (2368+u) || check (word5 (2368+u)) cert74[u]! = true := by decide +kernel
def cert75 : Array Nat := #[0, 58, 53653297, 0, 58, 53653298, 0, 0, 0, 74, 75, 74, 0, 74, 0, 0, 75, 74, 0, 0, 50, 50, 82, 50, 50, 82, 50, 50, 90, 82, 86, 82]
theorem block75 : ∀ u ∈ List.range 32, !valid5 (2400+u) || check (word5 (2400+u)) cert75[u]! = true := by decide +kernel
def cert76 : Array Nat := #[0, 82, 86, 90, 82, 0, 0, 90, 82, 86, 50, 50, 0, 50, 50, 70160304, 50, 50, 0, 0, 25890793, 54, 54, 82, 0, 54, 82, 0, 54, 90, 82, 0]
theorem block76 : ∀ u ∈ List.range 32, !valid5 (2432+u) || check (word5 (2432+u)) cert76[u]! = true := by decide +kernel
def cert77 : Array Nat := #[58, 58, 82, 58, 0, 82, 58, 0, 0, 82, 86, 50, 50, 25858032, 50, 50, 0, 50, 50, 70193065, 0, 0, 82, 0, 82, 0, 90, 82, 0, 0, 90, 82]
theorem block77 : ∀ u ∈ List.range 32, !valid5 (2464+u) || check (word5 (2464+u)) cert77[u]! = true := by decide +kernel
def cert78 : Array Nat := #[0, 82, 0, 82, 86, 0, 82, 0, 0, 0, 82, 86, 58, 58, 0, 58, 0, 70160305, 58, 0, 0, 0, 70160306, 50, 50, 0, 50, 50, 0, 50, 50, 0]
theorem block78 : ∀ u ∈ List.range 32, !valid5 (2496+u) || check (word5 (2496+u)) cert78[u]! = true := by decide +kernel
def cert79 : Array Nat := #[0, 0, 54, 54, 25858033, 0, 54, 0, 0, 54, 25858034, 0, 0, 52, 52, 52, 84, 52, 84, 85, 52, 52, 86, 84, 53, 0, 53, 84, 53, 84, 0, 0]
theorem block79 : ∀ u ∈ List.range 32, !valid5 (2528+u) || check (word5 (2528+u)) cert79[u]! = true := by decide +kernel

theorem portion9 (h : Nat) (lo : 2304≤h) (hi : h<2560) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t76 : h<2432
  ·
    by_cases t74 : h<2368
    ·
      by_cases t73 : h<2336
      ·
        have H := block72 (h-2304) (List.mem_range.mpr (by omega))
        have E : 2304+(h-2304)=h := by omega
        rw [E,valid] at H
        exact ⟨cert72[h-2304]!,by simpa using H⟩
      ·
        have H := block73 (h-2336) (List.mem_range.mpr (by omega))
        have E : 2336+(h-2336)=h := by omega
        rw [E,valid] at H
        exact ⟨cert73[h-2336]!,by simpa using H⟩
    ·
      by_cases t75 : h<2400
      ·
        have H := block74 (h-2368) (List.mem_range.mpr (by omega))
        have E : 2368+(h-2368)=h := by omega
        rw [E,valid] at H
        exact ⟨cert74[h-2368]!,by simpa using H⟩
      ·
        have H := block75 (h-2400) (List.mem_range.mpr (by omega))
        have E : 2400+(h-2400)=h := by omega
        rw [E,valid] at H
        exact ⟨cert75[h-2400]!,by simpa using H⟩
  ·
    by_cases t78 : h<2496
    ·
      by_cases t77 : h<2464
      ·
        have H := block76 (h-2432) (List.mem_range.mpr (by omega))
        have E : 2432+(h-2432)=h := by omega
        rw [E,valid] at H
        exact ⟨cert76[h-2432]!,by simpa using H⟩
      ·
        have H := block77 (h-2464) (List.mem_range.mpr (by omega))
        have E : 2464+(h-2464)=h := by omega
        rw [E,valid] at H
        exact ⟨cert77[h-2464]!,by simpa using H⟩
    ·
      by_cases t79 : h<2528
      ·
        have H := block78 (h-2496) (List.mem_range.mpr (by omega))
        have E : 2496+(h-2496)=h := by omega
        rw [E,valid] at H
        exact ⟨cert78[h-2496]!,by simpa using H⟩
      ·
        have H := block79 (h-2528) (List.mem_range.mpr (by omega))
        have E : 2528+(h-2528)=h := by omega
        rw [E,valid] at H
        exact ⟨cert79[h-2528]!,by simpa using H⟩
end BikovEight
