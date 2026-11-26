import Upper
import Mathlib.Data.Finset.Max

open SimpleGraph
namespace QuorumBounds

variable {V : Type} [Fintype V]

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

end
end QuorumBounds

namespace QuorumMinimum
open QuorumBounds

theorem psi_order_upper (n L : Nat) (lp : 0<L) (h : n≤2^L) :
    ∃ G : SimpleGraph (Fin n), psi G + psi Gᶜ ≤ 80*L := by
  obtain ⟨G,H⟩ := min_order_upper n L lp h
  obtain ⟨f,sf,vf⟩ := psi_achievable G
  obtain ⟨g,sg,vg⟩ := psi_achievable Gᶜ
  exact ⟨G,H _ _ f g sf sg vf vg⟩

#print axioms psi_order_upper
end QuorumMinimum
