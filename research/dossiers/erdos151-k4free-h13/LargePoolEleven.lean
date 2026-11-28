import LargePoolTen
import UnblockingTheorem

namespace Erdős151.H13
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangle_independent_eleven_transport {W : Type*} [Fintype W]
    (e : V ≃ W) (h : TriangleIndependentEleven W) : TriangleIndependentEleven V := by
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
theorem large_pool_free_eleven {G : V → V → Prop}
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (link : TriangleFreeLinks G)
    (R50 : ∀ n, 50 ≤ n → TriangleIndependentEleven (Fin n))
    (A : Finset V) (size : 50 ≤ A.card) :
    ∃ T : Finset V, T ⊆ A ∧ 11 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  let e := Fintype.equivFin ↥A
  have hn : 50 ≤ Fintype.card ↥A := by simpa only [Fintype.card_coe] using size
  have H := triangle_independent_eleven_transport e (R50 _ hn)
  let G' : ↥A → ↥A → Prop := fun a b => G a.val b.val
  obtain ⟨T,ht,hfree⟩ := k4free_of_triangle_independent_eleven G'
    (fun {_ _} h => sym h) (fun a => irr a.val)
    (fun w a b c wa wb wc ab bc ac => link w.val a.val b.val c.val wa wb wc ab bc ac)
    (by omega) H
  let emb : ↥A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨T.map emb,?_ ,by simpa only [Finset.card_map] using ht,H12.lift_induced_free A T hfree⟩
  intro x hx
  obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
  exact y.property

#print axioms large_pool_free_eleven
end Erdős151.H13
