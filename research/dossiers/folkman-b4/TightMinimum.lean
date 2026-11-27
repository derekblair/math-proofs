import TightBrace

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

def Nontrivial (s : Finset L) (t : Finset V) : Prop :=
  2 ≤ shore s t ∧ shore s t + 2 ≤ Fintype.card L + Fintype.card V

theorem complement_tight {I : L → V → Prop} (s : Finset L) (t : Finset V)
    (h : Tight I (fun l => decide (l∈s)) (fun v => decide (v∈t))) :
    Tight I (fun l => decide (l∈sᶜ)) (fun v => decide (v∈tᶜ)) := by
  intro m M
  have E (v : V) :
      (decide (m v∈sᶜ) ≠ decide (v∈tᶜ)) ↔
        decide (m v∈s) ≠ decide (v∈t) := by
    simp only [mem_compl,decide_not]
    cases decide (m v∈s) <;> cases decide (v∈t) <;> decide
  obtain ⟨v,hv,uniq⟩ := h m M
  exact ⟨v,(E v).mpr hv,fun w hw => uniq w ((E w).mp hw)⟩

theorem min_nontrivial (I : L → V → Prop) (h : ¬NoSmallCut I) :
    ∃ s : Finset L, ∃ t : Finset V, Nontrivial s t ∧
      Tight I (fun l => decide (l∈s)) (fun v => decide (v∈t)) ∧
      ∀ a b, Nontrivial a b →
        Tight I (fun l => decide (l∈a)) (fun v => decide (v∈b)) →
        shore s t ≤ shore a b := by
  classical
  have W : ∃ s : Finset L, ∃ t : Finset V, Nontrivial s t ∧
      Tight I (fun l => decide (l∈s)) (fun v => decide (v∈t)) := by
    unfold NoSmallCut at h
    push Not at h
    obtain ⟨s,t,h1,h2,ht⟩ := h
    exact ⟨s,t,⟨h1,h2⟩,ht⟩
  let P (n : Nat) := ∃ s : Finset L, ∃ t : Finset V, Nontrivial s t ∧
    Tight I (fun l => decide (l∈s)) (fun v => decide (v∈t)) ∧ shore s t=n
  have e : ∃ n, P n := by
    obtain ⟨s,t,hs,ht⟩ := W
    exact ⟨shore s t,s,t,hs,ht,rfl⟩
  obtain ⟨s,t,hs,ht,n⟩ := Nat.find_spec e
  exact ⟨s,t,hs,ht,fun a b hab hab' => n.symm ▸ Nat.find_min' e ⟨a,b,hab,hab',rfl⟩⟩

def inMembers (s : Finset L) : In (fun l => decide (l∈s)) ≃ {l : L // l∈s} :=
  Equiv.subtypeEquivRight fun _ => by simp

theorem card_inside (s : Finset L) :
    Fintype.card (In (fun l => decide (l∈s))) = s.card :=
  (Fintype.card_congr (inMembers s)).trans (Fintype.card_coe s)

#print axioms min_nontrivial
end FolkmanB4.Tight
