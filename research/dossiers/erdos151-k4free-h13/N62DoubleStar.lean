import N62OwnerGeometry

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

/-- Any set of exterior columns supported on P, all hitting one
owner by a lone edge, contains at most |P| columns. In particular
duplicated double-owner supports form a matching on the owners. -/
theorem independent_supported_count
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (S P Z : Finset V) (sc : S.card=12) (ps : P⊆S)
    (sf : Free (Forbidden G) (S : Set V))
    (upper : ∀ L : Finset V, Free (Forbidden G) (L : Set V) → L.card≤12)
    (out : Disjoint S Z)
    (indep : ∀ a∈Z, ∀ b∈Z, ¬G a b)
    (supp : ∀ z∈Z, support G S z⊆P) : Z.card≤P.card := by
  let R := S \ P
  have rs : R⊆S := Finset.sdiff_subset
  have rd := Finset.card_sdiff_add_card_eq_card ps
  have rZ : Disjoint R Z := out.mono_left rs
  have rf : Free (Forbidden G) (R : Set V) := fun T hT h => sf T hT (fun v hv => rs (h hv))
  have ad := free_adjoin_independent G sym irr R Z rf
    indep
    (fun z hz r hr h => (Finset.mem_sdiff.mp hr).2
      (supp z hz (Finset.mem_filter.mpr ⟨rs hr,h⟩)))
  have u := upper _ ad
  rw [Finset.card_union_of_disjoint rZ.symm] at u
  change R.card+P.card=S.card at rd
  omega

theorem pairwiseLone_supported_count
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (S P Z : Finset V) (sc : S.card=12) (ps : P⊆S)
    (sf : Free (Forbidden G) (S : Set V))
    (upper : ∀ L : Finset V, Free (Forbidden G) (L : Set V) → L.card≤12)
    (out : Disjoint S Z)
    (lone : ∀ a∈Z, ∀ b∈Z, ∃ g, Lone G g a ∧ Lone G g b)
    (supp : ∀ z∈Z, support G S z⊆P) : Z.card≤P.card :=
  independent_supported_count G sym irr S P Z sc ps sf upper out
    (fun a ha b hb => by
      obtain ⟨g,ga,gb⟩ := lone a ha b hb
      exact lone_neighbors_nonadjacent G sym ga gb.1) supp

theorem commonLone_supported_count
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (S P Z : Finset V) (sc : S.card=12) (ps : P⊆S)
    (sf : Free (Forbidden G) (S : Set V))
    (upper : ∀ L : Finset V, Free (Forbidden G) (L : Set V) → L.card≤12)
    (out : Disjoint S Z) (g : V)
    (lone : ∀ z∈Z, Lone G g z)
    (supp : ∀ z∈Z, support G S z⊆P) : Z.card≤P.card :=
  pairwiseLone_supported_count G sym irr S P Z sc ps sf upper out
    (fun a ha b hb => ⟨g,lone a ha,lone b hb⟩) supp

#print axioms commonLone_supported_count
#print axioms pairwiseLone_supported_count
end Erdos151N62
