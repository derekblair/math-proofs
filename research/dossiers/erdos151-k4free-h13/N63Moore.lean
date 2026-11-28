import N63MaxPivotBalance

namespace Erdos151N63
open scoped BigOperators

def AtMostOneCommon {V : Type*} (G : V → V → Prop) : Prop :=
  ∀ a b x y, a≠b → G a x → G b x → G a y → G b y → x=y

abbrev MooreSlots := Option (Fin 3 ⊕ (Fin 3 × Fin 2))

def mooreVal {V : Type*} (w : V) (L : Fin 3 → V) (M : Fin 3 → Fin 2 → V) : MooreSlots → V
  | none => w
  | some (Sum.inl i) => L i
  | some (Sum.inr (i,j)) => M i j

variable {V : Type*} [Fintype V] [DecidableEq V] (G : V → V → Prop) [DecidableRel G]

/-- A radius-two chart of a squareless cubic triangle-free graph attains the
Moore count 1+3+6. The latter six vertices are grouped by their parent. -/
theorem moore_blocks (hn : Fintype.card V=10)
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (sq : AtMostOneCommon G) (deg : ∀ v, fullDeg G v=3) :
    ∃ (w : V) (L : Fin 3 → V) (M : Fin 3 → Fin 2 → V),
      Function.Bijective (mooreVal w L M) ∧
      (∀ i, G w (L i)) ∧
      (∀ i j, ¬G w (M i j)) ∧
      (∀ i j k, G (L i) (M j k) ↔ i=j) := by
  classical
  have ne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let w := Classical.choice ne
  have hl : Fintype.card {z : V // G w z}=3 := (Fintype.card_subtype _).trans (deg w)
  let l := (Fintype.equivFinOfCardEq hl).symm
  let L (i : Fin 3) := (l i).val
  have wL (i : Fin 3) : G w (L i) := (l i).property
  have lc (i : Fin 3) : Fintype.card {z : V // z≠w ∧ G (L i) z}=2 := by
    let A := (Finset.univ : Finset V).filter (G (L i))
    have hw : w∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(sym _ _).mp (wL i)⟩
    have eq : A.erase w = Finset.univ.filter (fun z => z≠w ∧ G (L i) z) := by
      ext z
      simp [A]
    have ca := Finset.card_erase_add_one hw
    have da : A.card=3 := deg (L i)
    rw [Fintype.card_subtype,←eq]
    omega
  let m (i : Fin 3) := (Fintype.equivFinOfCardEq (lc i)).symm
  let M (i : Fin 3) (j : Fin 2) := (m i j).val
  have mN (i : Fin 3) (j : Fin 2) : M i j≠w := (m i j).property.1
  have mL (i : Fin 3) (j : Fin 2) : G (L i) (M i j) := (m i j).property.2
  have mW (i : Fin 3) (j : Fin 2) : ¬G w (M i j) :=
    fun h => tf _ _ _ (wL i) h (mL i j)
  have lI : Function.Injective L := fun a b h => l.injective (Subtype.ext h)
  have mI (i : Fin 3) : Function.Injective (M i) := fun a b h => (m i).injective (Subtype.ext h)
  have Lneq (i : Fin 3) : L i≠w := fun h => irr w (h ▸ wL i)
  have mt (i j : Fin 3) (k : Fin 2) : G (L i) (M j k) ↔ i=j := by
    constructor
    · intro h
      by_contra! hne
      have he := sq (L i) (L j) w (M j k) (fun eq => hne (lI eq))
        ((sym _ _).mp (wL i)) ((sym _ _).mp (wL j)) h (mL j k)
      exact mN j k he.symm
    · rintro rfl
      exact mL i k
  have cross (i k : Fin 3) (j : Fin 2) : L i≠M k j := fun h => mW k j (h ▸ wL i)
  have bij : Function.Bijective (mooreVal w L M) := by
    have inj : Function.Injective (mooreVal w L M) := by
      intro a b h
      rcases a with _|(a|⟨a,p⟩) <;> rcases b with _|(b|⟨b,q⟩)
      all_goals simp only [mooreVal] at h
      · rfl
      · exact False.elim (Lneq b h.symm)
      · exact False.elim (mN b q h.symm)
      · exact False.elim (Lneq a h)
      · exact congrArg (fun i => some (Sum.inl i)) (lI h)
      · exact False.elim (cross a b q h)
      · exact False.elim (mN a p h)
      · exact False.elim (cross b a p h.symm)
      · have hi : a=b := (mt a b q).mp (h ▸ mL a p)
        subst b
        have hp := mI a h
        subst q
        rfl
    exact ⟨inj,(Finite.injective_iff_surjective_of_equiv
      ((Fintype.equivFinOfCardEq (show Fintype.card MooreSlots=10 by decide)).trans
        (Fintype.equivFinOfCardEq hn).symm)).mp inj⟩
  exact ⟨w,L,M,bij,wL,mW,mt⟩

#print axioms moore_blocks
end Erdos151N63
