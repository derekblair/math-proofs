import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert312 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block312 : ∀ u ∈ List.range 32, !valid5 (9984+u) || check (word5 (9984+u)) cert312[u]! = true := by decide +kernel
def cert313 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block313 : ∀ u ∈ List.range 32, !valid5 (10016+u) || check (word5 (10016+u)) cert313[u]! = true := by decide +kernel
def cert314 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block314 : ∀ u ∈ List.range 32, !valid5 (10048+u) || check (word5 (10048+u)) cert314[u]! = true := by decide +kernel
def cert315 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block315 : ∀ u ∈ List.range 32, !valid5 (10080+u) || check (word5 (10080+u)) cert315[u]! = true := by decide +kernel
def cert316 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block316 : ∀ u ∈ List.range 32, !valid5 (10112+u) || check (word5 (10112+u)) cert316[u]! = true := by decide +kernel
def cert317 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block317 : ∀ u ∈ List.range 32, !valid5 (10144+u) || check (word5 (10144+u)) cert317[u]! = true := by decide +kernel
def cert318 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block318 : ∀ u ∈ List.range 32, !valid5 (10176+u) || check (word5 (10176+u)) cert318[u]! = true := by decide +kernel
def cert319 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block319 : ∀ u ∈ List.range 32, !valid5 (10208+u) || check (word5 (10208+u)) cert319[u]! = true := by decide +kernel

theorem portion39 (h : Nat) (lo : 9984≤h) (hi : h<10240) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t316 : h<10112
  ·
    by_cases t314 : h<10048
    ·
      by_cases t313 : h<10016
      ·
        have H := block312 (h-9984) (List.mem_range.mpr (by omega))
        have E : 9984+(h-9984)=h := by omega
        rw [E,valid] at H
        exact ⟨cert312[h-9984]!,by simpa using H⟩
      ·
        have H := block313 (h-10016) (List.mem_range.mpr (by omega))
        have E : 10016+(h-10016)=h := by omega
        rw [E,valid] at H
        exact ⟨cert313[h-10016]!,by simpa using H⟩
    ·
      by_cases t315 : h<10080
      ·
        have H := block314 (h-10048) (List.mem_range.mpr (by omega))
        have E : 10048+(h-10048)=h := by omega
        rw [E,valid] at H
        exact ⟨cert314[h-10048]!,by simpa using H⟩
      ·
        have H := block315 (h-10080) (List.mem_range.mpr (by omega))
        have E : 10080+(h-10080)=h := by omega
        rw [E,valid] at H
        exact ⟨cert315[h-10080]!,by simpa using H⟩
  ·
    by_cases t318 : h<10176
    ·
      by_cases t317 : h<10144
      ·
        have H := block316 (h-10112) (List.mem_range.mpr (by omega))
        have E : 10112+(h-10112)=h := by omega
        rw [E,valid] at H
        exact ⟨cert316[h-10112]!,by simpa using H⟩
      ·
        have H := block317 (h-10144) (List.mem_range.mpr (by omega))
        have E : 10144+(h-10144)=h := by omega
        rw [E,valid] at H
        exact ⟨cert317[h-10144]!,by simpa using H⟩
    ·
      by_cases t319 : h<10208
      ·
        have H := block318 (h-10176) (List.mem_range.mpr (by omega))
        have E : 10176+(h-10176)=h := by omega
        rw [E,valid] at H
        exact ⟨cert318[h-10176]!,by simpa using H⟩
      ·
        have H := block319 (h-10208) (List.mem_range.mpr (by omega))
        have E : 10208+(h-10208)=h := by omega
        rw [E,valid] at H
        exact ⟨cert319[h-10208]!,by simpa using H⟩
end BikovEight
