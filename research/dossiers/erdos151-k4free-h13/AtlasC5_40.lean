import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert320 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block320 : ∀ u ∈ List.range 32, !valid5 (10240+u) || check (word5 (10240+u)) cert320[u]! = true := by decide +kernel
def cert321 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block321 : ∀ u ∈ List.range 32, !valid5 (10272+u) || check (word5 (10272+u)) cert321[u]! = true := by decide +kernel
def cert322 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block322 : ∀ u ∈ List.range 32, !valid5 (10304+u) || check (word5 (10304+u)) cert322[u]! = true := by decide +kernel
def cert323 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block323 : ∀ u ∈ List.range 32, !valid5 (10336+u) || check (word5 (10336+u)) cert323[u]! = true := by decide +kernel
def cert324 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block324 : ∀ u ∈ List.range 32, !valid5 (10368+u) || check (word5 (10368+u)) cert324[u]! = true := by decide +kernel
def cert325 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block325 : ∀ u ∈ List.range 32, !valid5 (10400+u) || check (word5 (10400+u)) cert325[u]! = true := by decide +kernel
def cert326 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block326 : ∀ u ∈ List.range 32, !valid5 (10432+u) || check (word5 (10432+u)) cert326[u]! = true := by decide +kernel
def cert327 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block327 : ∀ u ∈ List.range 32, !valid5 (10464+u) || check (word5 (10464+u)) cert327[u]! = true := by decide +kernel

theorem portion40 (h : Nat) (lo : 10240≤h) (hi : h<10496) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t324 : h<10368
  ·
    by_cases t322 : h<10304
    ·
      by_cases t321 : h<10272
      ·
        have H := block320 (h-10240) (List.mem_range.mpr (by omega))
        have E : 10240+(h-10240)=h := by omega
        rw [E,valid] at H
        exact ⟨cert320[h-10240]!,by simpa using H⟩
      ·
        have H := block321 (h-10272) (List.mem_range.mpr (by omega))
        have E : 10272+(h-10272)=h := by omega
        rw [E,valid] at H
        exact ⟨cert321[h-10272]!,by simpa using H⟩
    ·
      by_cases t323 : h<10336
      ·
        have H := block322 (h-10304) (List.mem_range.mpr (by omega))
        have E : 10304+(h-10304)=h := by omega
        rw [E,valid] at H
        exact ⟨cert322[h-10304]!,by simpa using H⟩
      ·
        have H := block323 (h-10336) (List.mem_range.mpr (by omega))
        have E : 10336+(h-10336)=h := by omega
        rw [E,valid] at H
        exact ⟨cert323[h-10336]!,by simpa using H⟩
  ·
    by_cases t326 : h<10432
    ·
      by_cases t325 : h<10400
      ·
        have H := block324 (h-10368) (List.mem_range.mpr (by omega))
        have E : 10368+(h-10368)=h := by omega
        rw [E,valid] at H
        exact ⟨cert324[h-10368]!,by simpa using H⟩
      ·
        have H := block325 (h-10400) (List.mem_range.mpr (by omega))
        have E : 10400+(h-10400)=h := by omega
        rw [E,valid] at H
        exact ⟨cert325[h-10400]!,by simpa using H⟩
    ·
      by_cases t327 : h<10464
      ·
        have H := block326 (h-10432) (List.mem_range.mpr (by omega))
        have E : 10432+(h-10432)=h := by omega
        rw [E,valid] at H
        exact ⟨cert326[h-10432]!,by simpa using H⟩
      ·
        have H := block327 (h-10464) (List.mem_range.mpr (by omega))
        have E : 10464+(h-10464)=h := by omega
        rw [E,valid] at H
        exact ⟨cert327[h-10464]!,by simpa using H⟩
end BikovEight
