import UnblockingGraph

namespace Erdős151

variable {V : Type*}

def GraphClique (G : V → V → Prop) (S : Set V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G a b

def MaximalNontrivialClique (G : V → V → Prop) (S : Set V) : Prop :=
  GraphClique G S ∧ (∃ a ∈ S, ∃ b ∈ S, a ≠ b) ∧
    ∀ T : Set V, GraphClique G T → S ⊆ T → T ⊆ S

theorem forbidden_iff_maximal_nontrivial_clique (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (hlink : TriangleFreeLinks G) (S : Set V) :
    Forbidden G S ↔ MaximalNontrivialClique G S := by
  classical
  constructor
  · intro hS
    refine ⟨(fun a ha b hb hn => forbidden_clique G sym S hS a b ha hb hn), ?_, ?_⟩
    · rcases hS with ⟨a,b,rfl,hab,_⟩ | ⟨a,b,c,rfl,hab,_,_⟩
      all_goals refine ⟨a, by simp, b, by simp, ?_⟩
      all_goals rintro rfl; exact irr _ hab
    · intro T hT hST x hx
      by_contra hn
      rcases hS with ⟨a,b,rfl,_,hl⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
      · exact hl x ⟨hT a (hST (by simp)) x hx (by
            rintro rfl; exact hn (by simp)),
          hT b (hST (by simp)) x hx (by
            rintro rfl; exact hn (by simp))⟩
      · have hax := hT a (hST (by simp)) x hx (by rintro rfl; exact hn (by simp))
        have hbx := hT b (hST (by simp)) x hx (by rintro rfl; exact hn (by simp))
        have hcx := hT c (hST (by simp)) x hx (by rintro rfl; exact hn (by simp))
        exact hlink a b c x hab hac hax hbc hcx hbx
  · rintro ⟨hS,⟨a,ha,b,hb,hab⟩,hmax⟩
    have hgab := hS a ha b hb hab
    by_cases hp : S ⊆ ({a,b} : Set V)
    · have hs : S = {a,b} := Set.Subset.antisymm hp (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl|rfl <;> assumption)
      refine Or.inl ⟨a,b,hs,hgab,?_⟩
      intro x hx
      have hax : a ≠ x := by rintro rfl; exact irr _ hx.1
      have hbx : b ≠ x := by rintro rfl; exact irr _ hx.2
      have hT : Forbidden G ({a,b,x} : Set V) :=
        Or.inr ⟨a,b,x,rfl,hgab,hx.2,hx.1⟩
      have hsub : S ⊆ ({a,b,x} : Set V) := by
        rw [hs]
        intro z hz
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz ⊢
        aesop
      have hxS := hmax _ (fun a ha b hb hn => forbidden_clique G sym _ hT a b ha hb hn) hsub (show x ∈ ({a,b,x} : Set V) by simp)
      have hp' := hp hxS
      simp [hax.symm,hbx.symm] at hp'
    · obtain ⟨c,hc,hcp⟩ : ∃ c ∈ S, c ∉ ({a,b} : Set V) := by
        by_contra hnone
        exact hp (fun c hc => Classical.byContradiction (fun hn => hnone ⟨c,hc,hn⟩))
      have hca : c ≠ a := by rintro rfl; exact hcp (by simp)
      have hcb : c ≠ b := by rintro rfl; exact hcp (by simp)
      have hbc := hS b hb c hc hcb.symm
      have hac := hS a ha c hc hca.symm
      refine Or.inr ⟨a,b,c,Set.Subset.antisymm ?_ ?_,hgab,hbc,hac⟩
      · intro x hx
        by_contra hn
        have hax := hS a ha x hx (by rintro rfl; exact hn (by simp))
        have hbx := hS b hb x hx (by rintro rfl; exact hn (by simp))
        have hcx := hS c hc x hx (by rintro rfl; exact hn (by simp))
        exact hlink a b c x hgab hac hax hbc hcx hbx
      · intro x hx
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
        rcases hx with rfl|rfl|rfl <;> assumption

theorem free_iff_complement_hits (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (hlink : TriangleFreeLinks G) (S : Set V) :
    Free (Forbidden G) S ↔ ∀ T : Set V, MaximalNontrivialClique G T →
      ∃ x ∈ T, x ∉ S := by
  classical
  constructor
  · intro hf T hT
    by_contra hh
    exact hf T ((forbidden_iff_maximal_nontrivial_clique G sym irr hlink T).mpr hT)
      (fun x hx => Classical.byContradiction (fun hn => hh ⟨x,hx,hn⟩))
  · intro hf T hT hTS
    obtain ⟨x,hx,hx'⟩ := hf T ((forbidden_iff_maximal_nontrivial_clique G sym irr hlink T).mp hT)
    exact hx' (hTS hx)

#print axioms forbidden_iff_maximal_nontrivial_clique
#print axioms free_iff_complement_hits
end Erdős151
