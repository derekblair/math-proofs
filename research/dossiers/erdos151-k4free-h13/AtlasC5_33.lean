import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert264 : Array Nat := #[101, 35247165, 101, 0, 101, 101, 0, 26567166, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 106, 105, 105, 0, 105, 106, 0, 0, 105]
theorem block264 : ∀ u ∈ List.range 32, !valid5 (8448+u) || check (word5 (8448+u)) cert264[u]! = true := by decide +kernel
def cert265 : Array Nat := #[105, 106, 106, 23308915, 106, 0, 106, 106, 0, 0, 51734909, 106, 105, 6801011, 105, 105, 0, 105, 53896509, 0, 0, 105, 105, 105, 106, 105, 105, 0, 105, 106, 0, 0]
theorem block265 : ∀ u ∈ List.range 32, !valid5 (8480+u) || check (word5 (8480+u)) cert265[u]! = true := by decide +kernel
def cert266 : Array Nat := #[105, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 106, 105, 105, 0, 105, 106, 0, 0, 105, 105, 106, 106, 54154557, 106, 0, 106, 106, 0]
theorem block266 : ∀ u ∈ List.range 32, !valid5 (8512+u) || check (word5 (8512+u)) cert266[u]! = true := by decide +kernel
def cert267 : Array Nat := #[0, 34989118, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 51992957, 105, 105, 0, 105, 35247166]
theorem block267 : ∀ u ∈ List.range 32, !valid5 (8544+u) || check (word5 (8544+u)) cert267[u]! = true := by decide +kernel
def cert268 : Array Nat := #[0, 0, 105, 105, 105, 106, 105, 105, 0, 105, 106, 0, 0, 105, 105, 114, 114, 116, 114, 114, 0, 114, 114, 116, 0, 0, 114, 114, 116, 114, 114, 0]
theorem block268 : ∀ u ∈ List.range 32, !valid5 (8576+u) || check (word5 (8576+u)) cert268[u]! = true := by decide +kernel
def cert269 : Array Nat := #[114, 114, 116, 0, 0, 116, 116, 116, 42447475, 116, 0, 70640061, 116, 116, 0, 0, 114, 114, 25921651, 114, 114, 0, 114, 114, 72640381, 0, 0, 114, 114, 116, 114, 114]
theorem block269 : ∀ u ∈ List.range 32, !valid5 (8608+u) || check (word5 (8608+u)) cert269[u]! = true := by decide +kernel
def cert270 : Array Nat := #[0, 114, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114, 114, 70898109, 114, 114, 0, 114, 114, 5661694, 0, 0, 114, 114, 116, 114]
theorem block270 : ∀ u ∈ List.range 32, !valid5 (8640+u) || check (word5 (8640+u)) cert270[u]! = true := by decide +kernel
def cert271 : Array Nat := #[114, 0, 114, 114, 116, 0, 0, 116, 116, 116, 72898429, 116, 0, 5919742, 116, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block271 : ∀ u ∈ List.range 32, !valid5 (8672+u) || check (word5 (8672+u)) cert271[u]! = true := by decide +kernel

theorem portion33 (h : Nat) (lo : 8448≤h) (hi : h<8704) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t268 : h<8576
  ·
    by_cases t266 : h<8512
    ·
      by_cases t265 : h<8480
      ·
        have H := block264 (h-8448) (List.mem_range.mpr (by omega))
        have E : 8448+(h-8448)=h := by omega
        rw [E,valid] at H
        exact ⟨cert264[h-8448]!,by simpa using H⟩
      ·
        have H := block265 (h-8480) (List.mem_range.mpr (by omega))
        have E : 8480+(h-8480)=h := by omega
        rw [E,valid] at H
        exact ⟨cert265[h-8480]!,by simpa using H⟩
    ·
      by_cases t267 : h<8544
      ·
        have H := block266 (h-8512) (List.mem_range.mpr (by omega))
        have E : 8512+(h-8512)=h := by omega
        rw [E,valid] at H
        exact ⟨cert266[h-8512]!,by simpa using H⟩
      ·
        have H := block267 (h-8544) (List.mem_range.mpr (by omega))
        have E : 8544+(h-8544)=h := by omega
        rw [E,valid] at H
        exact ⟨cert267[h-8544]!,by simpa using H⟩
  ·
    by_cases t270 : h<8640
    ·
      by_cases t269 : h<8608
      ·
        have H := block268 (h-8576) (List.mem_range.mpr (by omega))
        have E : 8576+(h-8576)=h := by omega
        rw [E,valid] at H
        exact ⟨cert268[h-8576]!,by simpa using H⟩
      ·
        have H := block269 (h-8608) (List.mem_range.mpr (by omega))
        have E : 8608+(h-8608)=h := by omega
        rw [E,valid] at H
        exact ⟨cert269[h-8608]!,by simpa using H⟩
    ·
      by_cases t271 : h<8672
      ·
        have H := block270 (h-8640) (List.mem_range.mpr (by omega))
        have E : 8640+(h-8640)=h := by omega
        rw [E,valid] at H
        exact ⟨cert270[h-8640]!,by simpa using H⟩
      ·
        have H := block271 (h-8672) (List.mem_range.mpr (by omega))
        have E : 8672+(h-8672)=h := by omega
        rw [E,valid] at H
        exact ⟨cert271[h-8672]!,by simpa using H⟩
end BikovEight
