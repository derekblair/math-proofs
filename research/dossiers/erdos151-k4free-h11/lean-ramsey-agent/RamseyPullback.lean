import RamseySmall

namespace Erdos151Ramsey

theorem pullback_triangleFree {V W : Type*} (f : V → W) (R : W → W → Prop)
    (tf : TriangleFree R) : TriangleFree (fun a b => R (f a) (f b)) :=
  fun a b c hab hbc => tf (f a) (f b) (f c) hab hbc

theorem pullback_independence_cap {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (R : W → W → Prop) (k : Nat)
    (cap : ∀ T : Finset W, Independent R T → T.card ≤ k)
    (S : Finset V) (ind : Independent (fun a b => R (f a) (f b)) S) :
    S.card ≤ k := by
  have hi : Independent R (S.map f) := by
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
    exact ind u hu v hv
  simpa using cap (S.map f) hi

theorem triangleFree_fin_mono {n m k : Nat} (hn : n ≤ m)
    (h : ∃ R : Fin m → Fin m → Prop,
      (∀ a b, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧ TriangleFree R ∧
      (∀ S : Finset (Fin m), Independent R S → S.card ≤ k)) :
    ∃ R : Fin n → Fin n → Prop, (∀ a b, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧
      TriangleFree R ∧ (∀ S : Finset (Fin n), Independent R S → S.card ≤ k) := by
  obtain ⟨R, hs, hi, ht, hc⟩ := h
  let f : Fin n ↪ Fin m :=
    ⟨fun i => ⟨i.val, i.isLt.trans_le hn⟩, fun _ _ he => Fin.ext (congrArg (fun j : Fin m => j.val) he)⟩
  exact ⟨fun a b => R (f a) (f b), fun a b => hs (f a) (f b), fun a => hi (f a),
    pullback_triangleFree f R ht, pullback_independence_cap f R k hc⟩

#print axioms triangleFree_fin_mono
end Erdos151Ramsey
