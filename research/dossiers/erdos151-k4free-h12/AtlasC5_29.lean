import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert232 : Array Nat := #[0, 69, 69, 54416693, 69, 0, 85, 69, 0, 0, 26807294, 85, 69, 69, 71160245, 69, 77, 0, 69, 77, 24652862, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block232 : ∀ u ∈ List.range 32, !valid5 (7424+u) || check (word5 (7424+u)) cert232[u]! = true := by decide +kernel
def cert233 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 0, 69, 0, 85, 69, 0, 0, 0, 85, 69, 69, 0, 69, 77, 0, 69, 77]
theorem block233 : ∀ u ∈ List.range 32, !valid5 (7456+u) || check (word5 (7456+u)) cert233[u]! = true := by decide +kernel
def cert234 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 75, 77, 73, 7666100, 77, 73, 75, 60909949, 11332029, 0, 0, 0, 0, 0, 0, 0]
theorem block234 : ∀ u ∈ List.range 32, !valid5 (7488+u) || check (word5 (7488+u)) cert234[u]! = true := by decide +kernel
def cert235 : Array Nat := #[0, 0, 0, 0, 73, 73, 0, 77, 73, 27087349, 77, 73, 0, 0, 28075582, 73, 73, 75, 0, 73, 43833141, 0, 73, 75, 44164158, 0, 0, 0, 0, 0, 0, 0]
theorem block235 : ∀ u ∈ List.range 32, !valid5 (7520+u) || check (word5 (7520+u)) cert235[u]! = true := by decide +kernel
def cert236 : Array Nat := #[0, 0, 0, 0, 0, 73, 73, 75, 77, 73, 0, 77, 73, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block236 : ∀ u ∈ List.range 32, !valid5 (7552+u) || check (word5 (7552+u)) cert236[u]! = true := by decide +kernel
def cert237 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 73, 0, 77, 73, 0, 77, 73, 0, 0, 0, 73, 73, 75, 0]
theorem block237 : ∀ u ∈ List.range 32, !valid5 (7584+u) || check (word5 (7584+u)) cert237[u]! = true := by decide +kernel
def cert238 : Array Nat := #[73, 0, 0, 73, 75, 0, 0, 74, 75, 74, 24409652, 74, 90, 61236541, 75, 74, 90, 28075581, 74, 0, 74, 6181877, 74, 90, 0, 0, 74, 90, 11332030, 0, 0, 0]
theorem block238 : ∀ u ∈ List.range 32, !valid5 (7616+u) || check (word5 (7616+u)) cert238[u]! = true := by decide +kernel
def cert239 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 74, 75, 74, 0, 74, 90, 0, 75, 74, 90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 75]
theorem block239 : ∀ u ∈ List.range 32, !valid5 (7648+u) || check (word5 (7648+u)) cert239[u]! = true := by decide +kernel

theorem portion29 (h : Nat) (lo : 7424≤h) (hi : h<7680) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t236 : h<7552
  ·
    by_cases t234 : h<7488
    ·
      by_cases t233 : h<7456
      ·
        have H := block232 (h-7424) (List.mem_range.mpr (by omega))
        have E : 7424+(h-7424)=h := by omega
        rw [E,valid] at H
        exact ⟨cert232[h-7424]!,by simpa using H⟩
      ·
        have H := block233 (h-7456) (List.mem_range.mpr (by omega))
        have E : 7456+(h-7456)=h := by omega
        rw [E,valid] at H
        exact ⟨cert233[h-7456]!,by simpa using H⟩
    ·
      by_cases t235 : h<7520
      ·
        have H := block234 (h-7488) (List.mem_range.mpr (by omega))
        have E : 7488+(h-7488)=h := by omega
        rw [E,valid] at H
        exact ⟨cert234[h-7488]!,by simpa using H⟩
      ·
        have H := block235 (h-7520) (List.mem_range.mpr (by omega))
        have E : 7520+(h-7520)=h := by omega
        rw [E,valid] at H
        exact ⟨cert235[h-7520]!,by simpa using H⟩
  ·
    by_cases t238 : h<7616
    ·
      by_cases t237 : h<7584
      ·
        have H := block236 (h-7552) (List.mem_range.mpr (by omega))
        have E : 7552+(h-7552)=h := by omega
        rw [E,valid] at H
        exact ⟨cert236[h-7552]!,by simpa using H⟩
      ·
        have H := block237 (h-7584) (List.mem_range.mpr (by omega))
        have E : 7584+(h-7584)=h := by omega
        rw [E,valid] at H
        exact ⟨cert237[h-7584]!,by simpa using H⟩
    ·
      by_cases t239 : h<7648
      ·
        have H := block238 (h-7616) (List.mem_range.mpr (by omega))
        have E : 7616+(h-7616)=h := by omega
        rw [E,valid] at H
        exact ⟨cert238[h-7616]!,by simpa using H⟩
      ·
        have H := block239 (h-7648) (List.mem_range.mpr (by omega))
        have E : 7648+(h-7648)=h := by omega
        rw [E,valid] at H
        exact ⟨cert239[h-7648]!,by simpa using H⟩
end BikovEight
