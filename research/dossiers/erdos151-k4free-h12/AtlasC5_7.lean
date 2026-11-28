import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert56 : Array Nat := #[84, 54, 54, 0, 69, 54, 0, 69, 54, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 41, 42, 41, 41, 73, 41, 42, 73, 74]
theorem block56 : ∀ u ∈ List.range 32, !valid5 (1792+u) || check (word5 (1792+u)) cert56[u]! = true := by decide +kernel
def cert57 : Array Nat := #[41, 41, 41, 0, 41, 41, 74, 41, 0, 0, 74, 41, 41, 42, 42, 0, 42, 73, 42, 42, 73, 0, 0, 42, 45, 73, 45, 0, 73, 45, 0, 73]
theorem block57 : ∀ u ∈ List.range 32, !valid5 (1824+u) || check (word5 (1824+u)) cert57[u]! = true := by decide +kernel
def cert58 : Array Nat := #[74, 45, 0, 41, 42, 41, 41, 0, 41, 42, 0, 0, 41, 41, 58, 58, 74, 58, 73, 0, 58, 73, 74, 0, 0, 45, 0, 45, 0, 74, 45, 0]
theorem block58 : ∀ u ∈ List.range 32, !valid5 (1856+u) || check (word5 (1856+u)) cert58[u]! = true := by decide +kernel
def cert59 : Array Nat := #[0, 74, 45, 0, 41, 0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 58, 58, 0, 58, 73, 0]
theorem block59 : ∀ u ∈ List.range 32, !valid5 (1888+u) || check (word5 (1888+u)) cert59[u]! = true := by decide +kernel
def cert60 : Array Nat := #[58, 73, 0, 0, 0, 73, 73, 74, 0, 73, 0, 0, 73, 74, 0, 0, 50, 50, 52, 50, 50, 82, 50, 50, 52, 82, 84, 53, 0, 53, 84, 53]
theorem block60 : ∀ u ∈ List.range 32, !valid5 (1920+u) || check (word5 (1920+u)) cert60[u]! = true := by decide +kernel
def cert61 : Array Nat := #[82, 0, 0, 53, 82, 84, 50, 50, 0, 50, 50, 84, 50, 50, 0, 0, 84, 52, 52, 52, 0, 52, 82, 0, 52, 52, 82, 0, 58, 58, 82, 58]
theorem block61 : ∀ u ∈ List.range 32, !valid5 (1952+u) || check (word5 (1952+u)) cert61[u]! = true := by decide +kernel
def cert62 : Array Nat := #[0, 82, 58, 0, 0, 82, 84, 50, 50, 52, 50, 50, 0, 50, 50, 52, 0, 0, 53, 0, 53, 0, 53, 82, 0, 0, 53, 82, 0, 82, 0, 82]
theorem block62 : ∀ u ∈ List.range 32, !valid5 (1984+u) || check (word5 (1984+u)) cert62[u]! = true := by decide +kernel
def cert63 : Array Nat := #[84, 0, 82, 0, 0, 0, 82, 84, 58, 58, 0, 58, 0, 84, 58, 0, 0, 0, 84, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 52, 52]
theorem block63 : ∀ u ∈ List.range 32, !valid5 (2016+u) || check (word5 (2016+u)) cert63[u]! = true := by decide +kernel

theorem portion7 (h : Nat) (lo : 1792≤h) (hi : h<2048) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t60 : h<1920
  ·
    by_cases t58 : h<1856
    ·
      by_cases t57 : h<1824
      ·
        have H := block56 (h-1792) (List.mem_range.mpr (by omega))
        have E : 1792+(h-1792)=h := by omega
        rw [E,valid] at H
        exact ⟨cert56[h-1792]!,by simpa using H⟩
      ·
        have H := block57 (h-1824) (List.mem_range.mpr (by omega))
        have E : 1824+(h-1824)=h := by omega
        rw [E,valid] at H
        exact ⟨cert57[h-1824]!,by simpa using H⟩
    ·
      by_cases t59 : h<1888
      ·
        have H := block58 (h-1856) (List.mem_range.mpr (by omega))
        have E : 1856+(h-1856)=h := by omega
        rw [E,valid] at H
        exact ⟨cert58[h-1856]!,by simpa using H⟩
      ·
        have H := block59 (h-1888) (List.mem_range.mpr (by omega))
        have E : 1888+(h-1888)=h := by omega
        rw [E,valid] at H
        exact ⟨cert59[h-1888]!,by simpa using H⟩
  ·
    by_cases t62 : h<1984
    ·
      by_cases t61 : h<1952
      ·
        have H := block60 (h-1920) (List.mem_range.mpr (by omega))
        have E : 1920+(h-1920)=h := by omega
        rw [E,valid] at H
        exact ⟨cert60[h-1920]!,by simpa using H⟩
      ·
        have H := block61 (h-1952) (List.mem_range.mpr (by omega))
        have E : 1952+(h-1952)=h := by omega
        rw [E,valid] at H
        exact ⟨cert61[h-1952]!,by simpa using H⟩
    ·
      by_cases t63 : h<2016
      ·
        have H := block62 (h-1984) (List.mem_range.mpr (by omega))
        have E : 1984+(h-1984)=h := by omega
        rw [E,valid] at H
        exact ⟨cert62[h-1984]!,by simpa using H⟩
      ·
        have H := block63 (h-2016) (List.mem_range.mpr (by omega))
        have E : 2016+(h-2016)=h := by omega
        rw [E,valid] at H
        exact ⟨cert63[h-2016]!,by simpa using H⟩
end BikovEight
