import AtlasNumeric
namespace BikovEight
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cert216 : Array Nat := #[74, 82, 0, 0, 74, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 75, 74, 0, 74, 82, 0, 75, 74, 82, 0, 82, 6768251, 82]
theorem block216 : ∀ u ∈ List.range 32, !valid5 (6912+u) || check (word5 (6912+u)) cert216[u]! = true := by decide +kernel
def cert217 : Array Nat := #[86, 0, 82, 53900597, 0, 0, 82, 86, 74, 75, 74, 42414715, 74, 0, 70644149, 75, 74, 0, 0, 74, 0, 74, 0, 74, 82, 0, 0, 74, 82, 0, 82, 0]
theorem block217 : ∀ u ∈ List.range 32, !valid5 (6944+u) || check (word5 (6944+u)) cert217[u]! = true := by decide +kernel
def cert218 : Array Nat := #[82, 86, 0, 82, 0, 0, 0, 82, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74]
theorem block218 : ∀ u ∈ List.range 32, !valid5 (6976+u) || check (word5 (6976+u)) cert218[u]! = true := by decide +kernel
def cert219 : Array Nat := #[75, 74, 0, 74, 0, 0, 75, 74, 0, 0, 69, 69, 86, 69, 77, 84, 69, 77, 24652860, 86, 84, 84, 0, 86, 84, 51070075, 84, 0, 0, 5665781, 86, 84]
theorem block219 : ∀ u ∈ List.range 32, !valid5 (7008+u) || check (word5 (7008+u)) cert219[u]! = true := by decide +kernel
def cert220 : Array Nat := #[69, 69, 0, 69, 77, 84, 69, 77, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 86, 69, 0, 84, 69, 0, 0, 86]
theorem block220 : ∀ u ∈ List.range 32, !valid5 (7040+u) || check (word5 (7040+u)) cert220[u]! = true := by decide +kernel
def cert221 : Array Nat := #[84, 69, 69, 25888891, 69, 77, 0, 69, 77, 72644469, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 0, 86, 84, 0, 84, 0, 0, 0]
theorem block221 : ∀ u ∈ List.range 32, !valid5 (7072+u) || check (word5 (7072+u)) cert221[u]! = true := by decide +kernel
def cert222 : Array Nat := #[86, 84, 69, 69, 0, 69, 0, 84, 69, 0, 0, 0, 84, 69, 69, 0, 69, 77, 0, 69, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem block222 : ∀ u ∈ List.range 32, !valid5 (7104+u) || check (word5 (7104+u)) cert222[u]! = true := by decide +kernel
def cert223 : Array Nat := #[0, 0, 0, 73, 73, 74, 77, 73, 90, 77, 73, 74, 90, 72891260, 74, 0, 74, 34544251, 74, 90, 0, 0, 74, 90, 7666101, 73, 73, 0, 77, 73, 70190715, 77]
theorem block223 : ∀ u ∈ List.range 32, !valid5 (7136+u) || check (word5 (7136+u)) cert223[u]! = true := by decide +kernel

theorem portion27 (h : Nat) (lo : 6912≤h) (hi : h<7168) (valid : valid5 h=true) :
    ∃ v, check (word5 h) v=true := by
  by_cases t220 : h<7040
  ·
    by_cases t218 : h<6976
    ·
      by_cases t217 : h<6944
      ·
        have H := block216 (h-6912) (List.mem_range.mpr (by omega))
        have E : 6912+(h-6912)=h := by omega
        rw [E,valid] at H
        exact ⟨cert216[h-6912]!,by simpa using H⟩
      ·
        have H := block217 (h-6944) (List.mem_range.mpr (by omega))
        have E : 6944+(h-6944)=h := by omega
        rw [E,valid] at H
        exact ⟨cert217[h-6944]!,by simpa using H⟩
    ·
      by_cases t219 : h<7008
      ·
        have H := block218 (h-6976) (List.mem_range.mpr (by omega))
        have E : 6976+(h-6976)=h := by omega
        rw [E,valid] at H
        exact ⟨cert218[h-6976]!,by simpa using H⟩
      ·
        have H := block219 (h-7008) (List.mem_range.mpr (by omega))
        have E : 7008+(h-7008)=h := by omega
        rw [E,valid] at H
        exact ⟨cert219[h-7008]!,by simpa using H⟩
  ·
    by_cases t222 : h<7104
    ·
      by_cases t221 : h<7072
      ·
        have H := block220 (h-7040) (List.mem_range.mpr (by omega))
        have E : 7040+(h-7040)=h := by omega
        rw [E,valid] at H
        exact ⟨cert220[h-7040]!,by simpa using H⟩
      ·
        have H := block221 (h-7072) (List.mem_range.mpr (by omega))
        have E : 7072+(h-7072)=h := by omega
        rw [E,valid] at H
        exact ⟨cert221[h-7072]!,by simpa using H⟩
    ·
      by_cases t223 : h<7136
      ·
        have H := block222 (h-7104) (List.mem_range.mpr (by omega))
        have E : 7104+(h-7104)=h := by omega
        rw [E,valid] at H
        exact ⟨cert222[h-7104]!,by simpa using H⟩
      ·
        have H := block223 (h-7136) (List.mem_range.mpr (by omega))
        have E : 7136+(h-7136)=h := by omega
        rw [E,valid] at H
        exact ⟨cert223[h-7136]!,by simpa using H⟩
end BikovEight
