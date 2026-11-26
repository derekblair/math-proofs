import EdgeBridge
import Budget

namespace QuorumMinimum

open scoped BigOperators

section
variable {V C : Type} [Fintype V] [DecidableEq C]

def fiber (f : V → C) (c : C) : Finset V := Finset.univ.filter (fun v => f v = c)

noncomputable def localSame (G : SimpleGraph V) (f : V → C) (v : V) : Finset V := by
  classical
  exact (G.neighborFinset v).filter (fun u => f u = f v)

noncomputable def localOther (G : SimpleGraph V) (f : V → C) (v : V) : Finset V := by
  classical
  exact (G.neighborFinset v).filter (fun u => f u ≠ f v)

def Valid (G : SimpleGraph V) (f : V → C) : Prop :=
  ∀ v, (localOther G f v).card ≤ (localSame G f v).card + 1

open Classical in
theorem degree_le_color (G : SimpleGraph V) (f : V → C) (hf : Valid G f) (v : V) :
    G.degree v + 1 ≤ 2*(fiber f (f v)).card := by
  classical
  have sub : insert v (localSame G f v) ⊆ fiber f (f v) := by
    intro u hu
    rw [Finset.mem_insert] at hu
    rcases hu with rfl | hu
    · simp [fiber]
    · simpa [fiber] using (Finset.mem_filter.mp (show u ∈
        (G.neighborFinset v).filter (fun x => f x = f v) from hu)).2
  have notmem : v ∉ localSame G f v := by simp [localSame]
  have cap := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem notmem] at cap
  have part : (localSame G f v).card + (localOther G f v).card = G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_filter_add_card_filter_not (s := G.neighborFinset v) (fun u => f u = f v)
  have localok := hf v
  omega

theorem max_class_of_dense (G : SimpleGraph V) (f : V → C) (hf : Valid G f)
    (spos : 0 < Fintype.card V) (hd : Fintype.card V*(Fintype.card V-1) ≤ 8*ec G) :
    ∃ v : V, Fintype.card V + 3 ≤ 8*(fiber f (f v)).card := by
  classical
  have nu : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by simpa using spos)
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (fun u => (fiber f (f u)).card) nu
  refine ⟨v,?_⟩
  let s := Fintype.card V
  let M := (fiber f (f v)).card
  have cap (u : V) : G.degree u + 1 ≤ 2*M := by
    have a := degree_le_color G f hf u
    have b := hv u (Finset.mem_univ u)
    change (fiber f (f u)).card ≤ M at b
    omega
  have degsum : 2*ec G + s ≤ s*(2*M) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun u _ => cap u)
    rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges, ← ec_eq] at h
    simpa [s, Nat.mul_comm] using h
  have q := Nat.mul_le_mul_left 4 degsum
  have h1 : s*(s-1) ≤ 8*ec G := hd
  have sp : 0 < s := spos
  have hs : s-1+1=s := by omega
  have di := congrArg (s*·) hs
  simp only [Nat.mul_add,Nat.mul_one] at di
  have h2 : s*(s+3) ≤ s*(8*M) := by nlinarith only [q,h1,di]
  exact le_of_mul_le_mul_left h2 sp

end

#print axioms max_class_of_dense

end QuorumMinimum
