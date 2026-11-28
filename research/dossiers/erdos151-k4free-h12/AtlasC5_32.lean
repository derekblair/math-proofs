import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert256 : Array Nat := #[0, 0, 0, 101, 0, 101, 5919741, 101, 101, 0, 0, 101, 101, 24405566, 101, 0, 101, 105, 101, 101, 0, 0, 101, 101, 105, 105, 0, 105, 105, 7920061, 105, 0]
theorem block256 : ∀ u ∈ List.range 32, !valid5 (8192+u) || check (word5 (8192+u)) cert256[u]! = true := by decide +kernel
def cert257 : Array Nat := #[0, 24663614, 105, 105, 106, 106, 0, 106, 114, 106, 106, 114, 0, 0, 106, 106, 106, 0, 106, 114, 106, 106, 114, 0, 0, 106, 0, 0, 0, 0, 0, 0]
theorem block257 : ∀ u ∈ List.range 32, !valid5 (8224+u) || check (word5 (8224+u)) cert257[u]! = true := by decide +kernel
def cert258 : Array Nat := #[0, 0, 0, 0, 0, 106, 106, 0, 106, 114, 106, 106, 114, 0, 0, 106, 114, 114, 0, 114, 114, 70223475, 114, 114, 0, 0, 24405565, 106, 106, 0, 106, 53715571]
theorem block258 : ∀ u ∈ List.range 32, !valid5 (8256+u) || check (word5 (8256+u)) cert258[u]! = true := by decide +kernel
def cert259 : Array Nat := #[106, 106, 26567165, 0, 0, 106, 106, 106, 0, 106, 114, 106, 106, 114, 0, 0, 106, 114, 114, 0, 114, 114, 26825213, 114, 114, 0, 0, 7662014, 0, 0, 0, 0]
theorem block259 : ∀ u ∈ List.range 32, !valid5 (8288+u) || check (word5 (8288+u)) cert259[u]! = true := by decide +kernel
def cert260 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 106, 0, 106, 24663613, 106, 106, 7920062, 0, 0, 106, 101, 116, 101]
theorem block260 : ∀ u ∈ List.range 32, !valid5 (8320+u) || check (word5 (8320+u)) cert260[u]! = true := by decide +kernel
def cert261 : Array Nat := #[0, 101, 101, 0, 116, 101, 101, 0, 116, 116, 116, 0, 116, 71545971, 0, 116, 116, 34989117, 0, 101, 116, 101, 0, 101, 101, 0, 116, 101, 101, 0, 0, 0]
theorem block261 : ∀ u ∈ List.range 32, !valid5 (8352+u) || check (word5 (8352+u)) cert261[u]! = true := by decide +kernel
def cert262 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 101, 116, 101, 0, 101, 101, 0, 116, 101, 101, 0, 101, 5478515, 101, 0, 101, 101, 0, 43312957, 101, 101, 0, 0]
theorem block262 : ∀ u ∈ List.range 32, !valid5 (8384+u) || check (word5 (8384+u)) cert262[u]! = true := by decide +kernel
def cert263 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 116, 116, 0, 116, 43571005, 0, 116, 116, 26825214, 0, 101, 116, 101, 0, 101, 101, 0, 116, 101, 101, 0]
theorem block263 : ∀ u ∈ List.range 32, !valid5 (8416+u) || check (word5 (8416+u)) cert263[u]! = true := by decide +kernel

theorem portion32 (h : Nat) (lo : 8192≤h) (hi : h<8448) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t260 : h<8320
  ·
    by_cases t258 : h<8256
    ·
      by_cases t257 : h<8224
      ·
        have H := block256 (h-8192) (List.mem_range.mpr (by omega))
        have E : 8192+(h-8192)=h := by omega
        rw [E,valid] at H
        exact ⟨cert256[h-8192]!,by simpa using H⟩
      ·
        have H := block257 (h-8224) (List.mem_range.mpr (by omega))
        have E : 8224+(h-8224)=h := by omega
        rw [E,valid] at H
        exact ⟨cert257[h-8224]!,by simpa using H⟩
    ·
      by_cases t259 : h<8288
      ·
        have H := block258 (h-8256) (List.mem_range.mpr (by omega))
        have E : 8256+(h-8256)=h := by omega
        rw [E,valid] at H
        exact ⟨cert258[h-8256]!,by simpa using H⟩
      ·
        have H := block259 (h-8288) (List.mem_range.mpr (by omega))
        have E : 8288+(h-8288)=h := by omega
        rw [E,valid] at H
        exact ⟨cert259[h-8288]!,by simpa using H⟩
  ·
    by_cases t262 : h<8384
    ·
      by_cases t261 : h<8352
      ·
        have H := block260 (h-8320) (List.mem_range.mpr (by omega))
        have E : 8320+(h-8320)=h := by omega
        rw [E,valid] at H
        exact ⟨cert260[h-8320]!,by simpa using H⟩
      ·
        have H := block261 (h-8352) (List.mem_range.mpr (by omega))
        have E : 8352+(h-8352)=h := by omega
        rw [E,valid] at H
        exact ⟨cert261[h-8352]!,by simpa using H⟩
    ·
      by_cases t263 : h<8416
      ·
        have H := block262 (h-8384) (List.mem_range.mpr (by omega))
        have E : 8384+(h-8384)=h := by omega
        rw [E,valid] at H
        exact ⟨cert262[h-8384]!,by simpa using H⟩
      ·
        have H := block263 (h-8416) (List.mem_range.mpr (by omega))
        have E : 8416+(h-8416)=h := by omega
        rw [E,valid] at H
        exact ⟨cert263[h-8416]!,by simpa using H⟩
end BikovEight
