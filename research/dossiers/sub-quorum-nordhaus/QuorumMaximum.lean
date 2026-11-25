import QuorumNordhaus
import Mathlib.Data.Finset.Max

open SimpleGraph
namespace QuorumBounds

universe u
variable {V : Type u} [Fintype V]

noncomputable section

def Achievable (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ f : V → Option (Fin k), (∀ i, ∃ x, f x = some i) ∧ IsSubQuorum G f

theorem achievable_le {G : SimpleGraph V} {k : Nat} (h : Achievable G k) :
    k ≤ Fintype.card V := by
  classical
  obtain ⟨f,hf,_⟩ := h
  choose w hw using hf
  have hi : Function.Injective w := by
    intro i j he
    exact Option.some.inj ((hw i).symm.trans (he ▸ hw j))
  simpa using Fintype.card_le_of_injective w hi

def admissible (G : SimpleGraph V) : Finset Nat :=
  open Classical in (Finset.range (Fintype.card V + 1)).filter (Achievable G)

theorem mem_admissible (G : SimpleGraph V) (k : Nat) :
    k ∈ admissible G ↔ Achievable G k := by
  classical
  simp only [admissible,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  exact ⟨And.right,fun h => ⟨achievable_le h,h⟩⟩

theorem zero_admissible (G : SimpleGraph V) : 0 ∈ admissible G := by
  apply (mem_admissible G _).mpr
  refine ⟨fun _ => none,fun i => i.elim0,?_⟩
  exact fun _ i => Fin.elim0 i

/-- The maximum number of colors in the article's Definition 2.2. -/
def psi (G : SimpleGraph V) : Nat := (admissible G).max' ⟨0,zero_admissible G⟩

theorem psi_achievable (G : SimpleGraph V) : Achievable G (psi G) :=
  (mem_admissible G _).mp (Finset.max'_mem _ _)

theorem achievable_le_psi {G : SimpleGraph V} {k : Nat} (h : Achievable G k) :
    k ≤ psi G :=
  (admissible G).le_max' k ((mem_admissible G _).mpr h)

/-- Conjecture 9.2 in numeric form using the two genuine optimum values. -/
theorem conjecture9_2 (G : SimpleGraph V) : psi G + psi Gᶜ ≤ Fintype.card V + 2 := by
  obtain ⟨f,hf,h₁⟩ := psi_achievable G
  obtain ⟨g,hg,h₂⟩ := psi_achievable Gᶜ
  simpa using nordhausGaddum hf hg h₁ h₂

theorem empty_achieves (n : Nat) : Achievable (⊥ : SimpleGraph (Fin n)) n := by
  classical
  refine ⟨some,fun i => ⟨i,rfl⟩,?_⟩
  intro x i hi
  simp [others]

theorem two_vertices_colorable (G : SimpleGraph V) {x y : V} (hxy : x ≠ y) :
    Achievable G 2 := by
  classical
  let f (v : V) : Option (Fin 2) := if v = x then some 0 else if v = y then some 1 else none
  refine ⟨f,?_ ,?_⟩
  · intro i
    fin_cases i
    · exact ⟨x,by simp [f]⟩
    · exact ⟨y,by simp [f,hxy.symm]⟩
  · intro v i hi
    have h : (others G f v i) ⊆ ({x,y} : Finset V).erase v := by
      intro w hw
      simp only [others,Finset.mem_filter,Finset.mem_univ,true_and] at hw
      refine Finset.mem_erase.mpr ⟨hw.1.ne', ?_⟩
      obtain ⟨j,hj,_⟩ := hw.2
      by_cases h₁ : w = x
      · simp [h₁]
      · by_cases h₂ : w = y
        · simp [h₂]
        · simp [f,h₁,h₂] at hj
    have hv : v ∈ ({x,y} : Finset V) := by
      by_cases h : v = x
      · simp [h]
      · by_cases hh : v = y
        · simp [hh]
        · simp [f,h,hh] at hi
    have hh := Finset.card_le_card h
    rw [Finset.card_erase_of_mem hv] at hh
    simp [hxy] at hh
    omega

theorem sharp_on_empty (n : Nat) (hn : 2 ≤ n) :
    let G : SimpleGraph (Fin n) := ⊥
    psi G + psi Gᶜ = n + 2 := by
  dsimp only
  apply le_antisymm
  · simpa using conjecture9_2 (⊥ : SimpleGraph (Fin n))
  · have h₁ := achievable_le_psi (empty_achieves n)
    have h₂ := achievable_le_psi
      (two_vertices_colorable (⊥ : SimpleGraph (Fin n))ᶜ
        (x := ⟨0,by omega⟩) (y := ⟨1,by omega⟩) (by intro h; cases h))
    omega

#print axioms conjecture9_2
#print axioms sharp_on_empty
end
end QuorumBounds
#print axioms QuorumBounds.subQuorum_iff_closed
