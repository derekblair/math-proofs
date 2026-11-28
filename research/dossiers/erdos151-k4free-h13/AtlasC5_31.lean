import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert248 : Array Nat := #[0, 0, 0, 0, 0, 0, 84, 0, 86, 84, 0, 84, 0, 0, 0, 86, 84, 84, 85, 0, 84, 0, 84, 85, 0, 0, 0, 84, 0, 0, 0, 0]
theorem block248 : ∀ u ∈ List.range 32, !valid5 (7936+u) || check (word5 (7936+u)) cert248[u]! = true := by decide +kernel
def cert249 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101, 106, 101, 105, 101, 101, 106, 114, 101, 101, 105, 106, 106, 116]
theorem block249 : ∀ u ∈ List.range 32, !valid5 (7968+u) || check (word5 (7968+u)) cert249[u]! = true := by decide +kernel
def cert250 : Array Nat := #[106, 114, 106, 106, 114, 116, 26825212, 106, 101, 116, 101, 105, 101, 101, 35247164, 116, 101, 101, 105, 105, 106, 105, 105, 114, 105, 106, 114, 24663612, 105, 105, 101, 114]
theorem block250 : ∀ u ∈ List.range 32, !valid5 (8000+u) || check (word5 (8000+u)) cert250[u]! = true := by decide +kernel
def cert251 : Array Nat := #[101, 114, 101, 101, 114, 114, 101, 101, 72898428, 101, 106, 101, 105, 101, 101, 106, 7920060, 101, 101, 105, 106, 106, 34989116, 106, 114, 106, 106, 114, 11170805, 44168245, 106, 114]
theorem block251 : ∀ u ∈ List.range 32, !valid5 (8032+u) || check (word5 (8032+u)) cert251[u]! = true := by decide +kernel
def cert252 : Array Nat := #[114, 116, 114, 114, 7662012, 114, 114, 116, 60914037, 11336117, 101, 116, 101, 24405564, 101, 101, 61240629, 116, 101, 101, 28079669, 101, 26567164, 101, 105, 101, 101, 77984181, 28406261, 101, 101, 105]
theorem block252 : ∀ u ∈ List.range 32, !valid5 (8064+u) || check (word5 (8064+u)) cert252[u]! = true := by decide +kernel
def cert253 : Array Nat := #[105, 106, 105, 105, 72640380, 105, 106, 45152053, 78149493, 105, 105, 101, 0, 101, 105, 101, 101, 0, 0, 101, 101, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block253 : ∀ u ∈ List.range 32, !valid5 (8096+u) || check (word5 (8096+u)) cert253[u]! = true := by decide +kernel
def cert254 : Array Nat := #[0, 101, 0, 101, 105, 101, 101, 0, 0, 101, 101, 105, 105, 0, 105, 105, 51102835, 105, 0, 0, 5661693, 105, 105, 101, 0, 101, 34577011, 101, 101, 0, 0, 101]
theorem block254 : ∀ u ∈ List.range 32, !valid5 (8128+u) || check (word5 (8128+u)) cert254[u]! = true := by decide +kernel
def cert255 : Array Nat := #[101, 7662013, 101, 0, 101, 105, 101, 101, 0, 0, 101, 101, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block255 : ∀ u ∈ List.range 32, !valid5 (8160+u) || check (word5 (8160+u)) cert255[u]! = true := by decide +kernel

theorem portion31 (h : Nat) (lo : 7936≤h) (hi : h<8192) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t252 : h<8064
  ·
    by_cases t250 : h<8000
    ·
      by_cases t249 : h<7968
      ·
        have H := block248 (h-7936) (List.mem_range.mpr (by omega))
        have E : 7936+(h-7936)=h := by omega
        rw [E,valid] at H
        exact ⟨cert248[h-7936]!,by simpa using H⟩
      ·
        have H := block249 (h-7968) (List.mem_range.mpr (by omega))
        have E : 7968+(h-7968)=h := by omega
        rw [E,valid] at H
        exact ⟨cert249[h-7968]!,by simpa using H⟩
    ·
      by_cases t251 : h<8032
      ·
        have H := block250 (h-8000) (List.mem_range.mpr (by omega))
        have E : 8000+(h-8000)=h := by omega
        rw [E,valid] at H
        exact ⟨cert250[h-8000]!,by simpa using H⟩
      ·
        have H := block251 (h-8032) (List.mem_range.mpr (by omega))
        have E : 8032+(h-8032)=h := by omega
        rw [E,valid] at H
        exact ⟨cert251[h-8032]!,by simpa using H⟩
  ·
    by_cases t254 : h<8128
    ·
      by_cases t253 : h<8096
      ·
        have H := block252 (h-8064) (List.mem_range.mpr (by omega))
        have E : 8064+(h-8064)=h := by omega
        rw [E,valid] at H
        exact ⟨cert252[h-8064]!,by simpa using H⟩
      ·
        have H := block253 (h-8096) (List.mem_range.mpr (by omega))
        have E : 8096+(h-8096)=h := by omega
        rw [E,valid] at H
        exact ⟨cert253[h-8096]!,by simpa using H⟩
    ·
      by_cases t255 : h<8160
      ·
        have H := block254 (h-8128) (List.mem_range.mpr (by omega))
        have E : 8128+(h-8128)=h := by omega
        rw [E,valid] at H
        exact ⟨cert254[h-8128]!,by simpa using H⟩
      ·
        have H := block255 (h-8160) (List.mem_range.mpr (by omega))
        have E : 8160+(h-8160)=h := by omega
        rw [E,valid] at H
        exact ⟨cert255[h-8160]!,by simpa using H⟩
end BikovEight
