import H10Theorem

namespace Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lift_induced_free {G : V → V → Prop} (A : Finset V) (T : Finset ↥A)
    (hT : Free (Forbidden (fun x y : ↥A => G x.val y.val)) (T : Set ↥A)) :
    Free (Forbidden G) ((T.map (⟨Subtype.val,Subtype.val_injective⟩ : ↥A ↪ V)) : Set V) := by
  classical
  let emb : ↥A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  intro B hB hsub
  change B ⊆ (↑(T.map emb) : Set V) at hsub
  rcases hB with ⟨a,b,rfl,ha⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp (hsub (show a ∈ ({a,b} : Set V) by simp))
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp (hsub (show b ∈ ({emb x,b} : Set V) by simp))
    have hl : Lone (fun x y : ↥A => G x.val y.val) x y :=
      ⟨ha.1,fun z hz => ha.2 z.val hz⟩
    exact hT {x,y} (Or.inl ⟨x,y,rfl,hl⟩) (by
      intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl|rfl
      · exact hx
      · exact hy)
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp (hsub (show a ∈ ({a,b,c} : Set V) by simp))
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp (hsub (show b ∈ ({emb x,b,c} : Set V) by simp))
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp (hsub (show c ∈ ({emb x,emb y,c} : Set V) by simp))
    exact hT {x,y,z} (Or.inr ⟨x,y,z,rfl,hab,hbc,hac⟩) (by
      intro t ht
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
      rcases ht with rfl|rfl|rfl
      · exact hx
      · exact hy
      · exact hz)

theorem triangle_independent_ten_transport {W : Type*} [Fintype W]
    (e : V ≃ W) (h : H10.TriangleIndependentTen W) : H10.TriangleIndependentTen V := by
  classical
  intro G sym irr triangle
  let G' : W → W → Prop := fun a b => G (e.symm a) (e.symm b)
  obtain ⟨S,card,ind⟩ := h G' (fun {_ _} a => sym a) (fun x => irr (e.symm x))
    (fun a b c ab bc => triangle (e.symm a) (e.symm b) (e.symm c) ab bc)
  let emb := e.symm.toEmbedding
  refine ⟨S.map emb,by simpa only [Finset.card_map] using card,?_⟩
  intro a ha b hb
  obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
  exact ind x hx y hy

/-- The only external mathematics in this bridge is the explicit
finite Ramsey upper-bound hypothesis, not an added Lean axiom. -/
theorem large_pool_free_ten {G : V → V → Prop}
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → H10.TriangleIndependentTen (Fin n))
    (A : Finset V) (size : 41 ≤ A.card) :
    ∃ T : Finset V, T ⊆ A ∧ 10 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  let e := Fintype.equivFin ↥A
  have hn : 41 ≤ Fintype.card ↥A := by simpa only [Fintype.card_coe] using size
  have H := triangle_independent_ten_transport e (R41 _ hn)
  let G' : ↥A → ↥A → Prop := fun a b => G a.val b.val
  obtain ⟨T,ht,hfree⟩ := H10.k4free_of_triangle_independent_ten G'
    (fun {_ _} h => sym h) (fun a => irr a.val)
    (fun w a b c wa wb wc ab bc ac => link w.val a.val b.val c.val wa wb wc ab bc ac)
    (by omega) H
  let emb : ↥A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨T.map emb,?_ ,by simpa only [Finset.card_map] using ht,lift_induced_free A T hfree⟩
  intro x hx
  obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
  exact y.property

#print axioms lift_induced_free
#print axioms large_pool_free_ten
end Erdős151.H12
