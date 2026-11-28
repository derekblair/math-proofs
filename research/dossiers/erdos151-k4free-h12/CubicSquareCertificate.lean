import WagnerHallMatching
import MatchedColor

open scoped BigOperators
namespace Erdős151.H12.Wagner

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def coTriangle (edge : E → Finset V) (a b : V) : Prop :=
  ∃ t, a ∈ edge t ∧ b ∈ edge t

theorem Steps.concat {R : V→V→Prop} {n m : Nat} {a b c : V}
    (p : Erdős151.H12.Steps R n a b) (q : Erdős151.H12.Steps R m b c) :
    ∃ k, Erdős151.H12.Steps R k a c := by
  induction p with
  | zero a => exact ⟨m,q⟩
  | more h _ ih =>
    obtain ⟨k,hk⟩ := ih q
    exact ⟨k+1,Erdős151.H12.Steps.more h hk⟩

theorem co_triangle_to_weak (m : V ≃ E) (edge : E → Finset V)
    {a b : V} (h : coTriangle edge a b) :
    ∃ n, Erdős151.H12.Steps (fun x y => matchedArc m edge x y ∨ matchedArc m edge y x) n a b := by
  classical
  obtain ⟨t,ha,hb⟩ := h
  let w := m.symm t
  have he : m w = t := m.apply_symm_apply t
  have p : ∃ n, Erdős151.H12.Steps
      (fun x y => matchedArc m edge x y ∨ matchedArc m edge y x) n a w := by
    by_cases q : a=w
    · subst a
      exact ⟨0, Erdős151.H12.Steps.zero w⟩
    · exact ⟨1,Erdős151.H12.Steps.more (Or.inr ⟨fun h => q h.symm,he.symm ▸ ha⟩)
        (Erdős151.H12.Steps.zero w)⟩
  have q : ∃ n, Erdős151.H12.Steps
      (fun x y => matchedArc m edge x y ∨ matchedArc m edge y x) n w b := by
    by_cases q : w=b
    · subst b
      exact ⟨0,Erdős151.H12.Steps.zero w⟩
    · exact ⟨1,Erdős151.H12.Steps.more (Or.inl ⟨q,he.symm ▸ hb⟩)
        (Erdős151.H12.Steps.zero b)⟩
  obtain ⟨_,p⟩ := p
  obtain ⟨_,q⟩ := q
  exact Steps.concat p q

theorem weak_contraction_paths (m : V ≃ E) (edge : E → Finset V)
    {n : Nat} {a b : V} (p : Erdős151.H12.Steps (coTriangle edge) n a b) :
    ∃ n, Erdős151.H12.Steps (fun x y => matchedArc m edge x y ∨ matchedArc m edge y x) n a b := by
  induction p with
  | zero a => exact ⟨0,Erdős151.H12.Steps.zero a⟩
  | more h _ ih =>
    obtain ⟨_,one⟩ := co_triangle_to_weak m edge h
    obtain ⟨_,tail⟩ := ih
    exact Steps.concat one tail

/-- A verifiable combinatorial certificate for coloring a connected
cubic triangle-incidence graph. Graph-specific work is now limited to
the short cut inequality, the local square data, and co-triangle paths. -/
theorem cubic_coloring_of_square_certificate
    (edge : E → Finset V)
    (row : ∀ e, (∑ v : V, if v ∈ edge e then (1:ℕ) else 0) = 3)
    (col : ∀ v, (∑ e : E, if v ∈ edge e then (1:ℕ) else 0) = 3)
    (P : Finset V) (B : Finset E) (h4 : B.card = 4)
    (m0 : ↥P ≃ ↥B) (local_mem : ∀ v, v.val ∈ edge (m0 v).val)
    (onLeft : ∀ s, s∉P → ∀ t∈B, ∀ u∈B, s ∈ edge t → s ∈ edge u → t=u)
    (onRight : ∀ t∈B, ∀ s, s∉P → ∀ u, u∉P → s ∈ edge t → u ∈ edge t → s=u)
    (small : ∀ S : Finset V, ∀ T : Finset E,
      Disjoint S P → 3 ≤ S.card → cutMass (fun v e => v∈edge e) S T ≤ 5 →
        mass (fun v e => v∈edge e) S T < S.card + T.card)
    (p : V) (hp : p∈P)
    (connected : ∀ v, ∃ n, Erdős151.H12.Steps (coTriangle edge) n v p)
    (base : V → Bool)
    (alt : ∀ v : ↥P, ∃ w : ↥P, v.val ≠ w.val ∧
      w.val ∈ edge (m0 v).val ∧ base v.val ≠ base w.val) :
    ∃ c : V → Bool, ∀ e, Mixed c (edge e) := by
  classical
  obtain ⟨m,hm,ext⟩ := matching_extends_square (fun v e => v ∈ edge e)
    col row P B h4 m0 local_mem onLeft onRight small
  refine matched_color_from_alternating_root m edge hm row col (fun v => v∈P) base p hp ?_ ?_
  · intro v
    obtain ⟨n,p⟩ := connected v
    exact weak_contraction_paths m edge p
  · intro v hv
    obtain ⟨w,ne,hw,diff⟩ := alt ⟨v,hv⟩
    refine ⟨w.val,⟨ne,?_⟩,w.property,diff⟩
    rw [ext ⟨v,hv⟩]
    exact hw

#print axioms weak_contraction_paths
#print axioms cubic_coloring_of_square_certificate
end Erdős151.H12.Wagner
