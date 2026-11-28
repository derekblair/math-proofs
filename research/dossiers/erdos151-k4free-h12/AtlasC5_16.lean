import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert128 : Array Nat := #[50, 0, 50, 50, 0, 0, 0, 52, 52, 52, 0, 52, 0, 0, 52, 52, 0, 0, 37, 0, 37, 41, 37, 37, 0, 0, 37, 37, 41, 37, 0, 37]
theorem block128 : ∀ u ∈ List.range 32, !valid5 (4096+u) || check (word5 (4096+u)) cert128[u]! = true := by decide +kernel
def cert129 : Array Nat := #[41, 37, 37, 0, 0, 37, 37, 41, 43, 0, 0, 43, 23243451, 43, 0, 0, 0, 0, 43, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 41, 0]
theorem block129 : ∀ u ∈ List.range 32, !valid5 (4128+u) || check (word5 (4128+u)) cert129[u]! = true := by decide +kernel
def cert130 : Array Nat := #[41, 41, 0, 41, 0, 0, 0, 41, 41, 53, 0, 53, 71480507, 53, 0, 0, 0, 53, 0, 0, 37, 0, 37, 0, 37, 37, 0, 0, 37, 37, 0, 41]
theorem block130 : ∀ u ∈ List.range 32, !valid5 (4160+u) || check (word5 (4160+u)) cert130[u]! = true := by decide +kernel
def cert131 : Array Nat := #[0, 41, 41, 0, 41, 0, 0, 0, 41, 41, 43, 0, 0, 43, 0, 43, 0, 0, 0, 0, 43, 26545660, 0, 0, 35255341, 52001133, 0, 0, 0, 0, 0, 0]
theorem block131 : ∀ u ∈ List.range 32, !valid5 (4192+u) || check (word5 (4192+u)) cert131[u]! = true := by decide +kernel
def cert132 : Array Nat := #[53, 0, 53, 0, 53, 0, 0, 0, 53, 0, 0, 42, 42, 0, 42, 50, 42, 42, 50, 0, 0, 42, 43, 0, 0, 43, 6735547, 43, 0, 0, 0, 0]
theorem block132 : ∀ u ∈ List.range 32, !valid5 (4224+u) || check (word5 (4224+u)) cert132[u]! = true := by decide +kernel
def cert133 : Array Nat := #[43, 42, 42, 0, 42, 50, 42, 42, 50, 0, 0, 42, 54, 54, 0, 0, 54, 42382011, 0, 54, 0, 0, 0, 42, 42, 0, 42, 0, 42, 42, 0, 0]
theorem block133 : ∀ u ∈ List.range 32, !valid5 (4256+u) || check (word5 (4256+u)) cert133[u]! = true := by decide +kernel
def cert134 : Array Nat := #[0, 42, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 34971196, 0, 0, 0, 54162733, 70906285, 0, 0, 0, 0, 0, 43, 0, 0, 43, 0, 43, 0, 0]
theorem block134 : ∀ u ∈ List.range 32, !valid5 (4288+u) || check (word5 (4288+u)) cert134[u]! = true := by decide +kernel
def cert135 : Array Nat := #[0, 0, 43, 42, 42, 0, 42, 0, 42, 42, 0, 0, 0, 42, 50, 50, 0, 50, 50, 0, 50, 50, 0, 0, 0, 54, 54, 0, 0, 54, 0, 0]
theorem block135 : ∀ u ∈ List.range 32, !valid5 (4320+u) || check (word5 (4320+u)) cert135[u]! = true := by decide +kernel

theorem portion16 (h : Nat) (lo : 4096≤h) (hi : h<4352) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t132 : h<4224
  ·
    by_cases t130 : h<4160
    ·
      by_cases t129 : h<4128
      ·
        have H := block128 (h-4096) (List.mem_range.mpr (by omega))
        have E : 4096+(h-4096)=h := by omega
        rw [E,valid] at H
        exact ⟨cert128[h-4096]!,by simpa using H⟩
      ·
        have H := block129 (h-4128) (List.mem_range.mpr (by omega))
        have E : 4128+(h-4128)=h := by omega
        rw [E,valid] at H
        exact ⟨cert129[h-4128]!,by simpa using H⟩
    ·
      by_cases t131 : h<4192
      ·
        have H := block130 (h-4160) (List.mem_range.mpr (by omega))
        have E : 4160+(h-4160)=h := by omega
        rw [E,valid] at H
        exact ⟨cert130[h-4160]!,by simpa using H⟩
      ·
        have H := block131 (h-4192) (List.mem_range.mpr (by omega))
        have E : 4192+(h-4192)=h := by omega
        rw [E,valid] at H
        exact ⟨cert131[h-4192]!,by simpa using H⟩
  ·
    by_cases t134 : h<4288
    ·
      by_cases t133 : h<4256
      ·
        have H := block132 (h-4224) (List.mem_range.mpr (by omega))
        have E : 4224+(h-4224)=h := by omega
        rw [E,valid] at H
        exact ⟨cert132[h-4224]!,by simpa using H⟩
      ·
        have H := block133 (h-4256) (List.mem_range.mpr (by omega))
        have E : 4256+(h-4256)=h := by omega
        rw [E,valid] at H
        exact ⟨cert133[h-4256]!,by simpa using H⟩
    ·
      by_cases t135 : h<4320
      ·
        have H := block134 (h-4288) (List.mem_range.mpr (by omega))
        have E : 4288+(h-4288)=h := by omega
        rw [E,valid] at H
        exact ⟨cert134[h-4288]!,by simpa using H⟩
      ·
        have H := block135 (h-4320) (List.mem_range.mpr (by omega))
        have E : 4320+(h-4320)=h := by omega
        rw [E,valid] at H
        exact ⟨cert135[h-4320]!,by simpa using H⟩
end BikovEight
