import TreeInfluenceMetric
import Mathlib.Data.Finset.Max

namespace TreeInfluence
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V]

noncomputable def ball (G : SimpleGraph V) (k : Nat) (a : V) : Finset V :=
  Finset.univ.filter fun x => G.dist a x ≤ k

noncomputable def scopes (G : SimpleGraph V) (k : Nat) : Finset (Finset V) :=
  (Finset.univ : Finset (V × V)).image fun p => ball G k p.1 ∩ ball G k p.2

noncomputable def interBalls (G : SimpleGraph V) (k : Nat) (C : Finset V) : Finset V :=
  Finset.univ.filter fun x => ∀ c ∈ C, G.dist c x ≤ k

theorem scopesCard (k : Nat) : (scopes G k).card ≤ (Fintype.card V)^2 := by
  simpa [scopes, pow_two] using
    (Finset.card_image_le (s := (Finset.univ : Finset (V × V)))
      (f := fun p => ball G k p.1 ∩ ball G k p.2))

theorem twoCenters (ht : G.IsTree) (k : Nat) (C : Finset V) (hn : C.Nonempty) :
    ∃ a ∈ C, ∃ b ∈ C, interBalls G k C = ball G k a ∩ ball G k b := by
  obtain ⟨⟨a,b⟩, hp, hh⟩ := (C ×ˢ C).exists_max_image (fun p => G.dist p.1 p.2)
    (by obtain ⟨c,hc⟩ := hn; exact ⟨(c,c), Finset.mem_product.mpr ⟨hc,hc⟩⟩)
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  refine ⟨a,ha,b,hb,?_⟩
  ext x
  simp only [interBalls, ball, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  refine ⟨fun hx => ⟨hx a ha,hx b hb⟩, fun ⟨hax,hbx⟩ c hc => ?_⟩
  have h₁ : G.dist a c ≤ G.dist a b := hh (a,c) (Finset.mem_product.mpr ⟨ha,hc⟩)
  have h₂ : G.dist b c ≤ G.dist a b := hh (b,c) (Finset.mem_product.mpr ⟨hb,hc⟩)
  have h₃ := fourPoint ht a b c x
  rw [le_max_iff] at h₃
  omega

theorem ballMemScopes (k : Nat) (x : V) : ball G k x ∈ scopes G k := by
  unfold scopes
  exact Finset.mem_image.mpr ⟨(x,x),Finset.mem_univ _, Finset.inter_self _⟩

theorem restrictMemScopes (ht : G.IsTree) (k : Nat) {S : Finset V}
    (h : S ∈ scopes G k) (x : V) : S ∩ ball G k x ∈ scopes G k := by
  obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp h
  obtain ⟨c,_,d,_,he⟩ := twoCenters ht k ({a,b,x} : Finset V) (by simp)
  refine Finset.mem_image.mpr ⟨(c,d), Finset.mem_univ _, ?_⟩
  rw [← he]
  ext y
  simp [ball, interBalls]

omit [DecidableEq V] in
theorem ballContainsPath (ht : G.IsTree) {a b c : V} {p : G.Walk a b}
    (hp : p.length = G.dist a b) (k : Nat) (ha : a ∈ ball G k c)
    (hb : b ∈ ball G k c) {x : V} (hx : x ∈ p.support) :
    x ∈ ball G k c := by
  obtain ⟨q,r,he⟩ := p.mem_support_iff_exists_append.mp hx
  have hq := G.length_eq_dist_of_subwalk hp (show q.IsSubwalk p from
    ⟨.nil,r,by simpa using he⟩)
  have hr := G.length_eq_dist_of_subwalk hp (show r.IsSubwalk p from
    ⟨q,.nil,by simpa using he⟩)
  have h₁ : G.dist a b = G.dist a x + G.dist x b := by
    calc
      _ = p.length := hp.symm
      _ = _ := by rw [he, Walk.length_append, hq, hr]
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
  have h₂ := fourPoint ht a b x c
  rw [G.dist_comm (u := x) (v := c), G.dist_comm (u := b) (v := c),
    G.dist_comm (u := a) (v := c), G.dist_comm (u := b) (v := x), le_max_iff] at h₂
  omega

theorem scopeContainsPath (ht : G.IsTree) (k : Nat) {S : Finset V} (hS : S ∈ scopes G k)
    {u v : (S : Set V)} {p : G.Walk u.val v.val} (hp : p.length = G.dist u.val v.val) :
    ∀ x ∈ p.support, x ∈ (S : Set V) := by
  obtain ⟨⟨a,b⟩,_,he⟩ := Finset.mem_image.mp hS
  intro x hx
  have hu : u.val ∈ ball G k a ∩ ball G k b := he ▸ u.property
  have hv : v.val ∈ ball G k a ∩ ball G k b := he ▸ v.property
  have hu' := Finset.mem_inter.mp hu
  have hv' := Finset.mem_inter.mp hv
  exact he ▸ Finset.mem_inter.mpr ⟨ballContainsPath ht hp k hu'.1 hv'.1 hx,
    ballContainsPath ht hp k hu'.2 hv'.2 hx⟩

theorem scopeDist (ht : G.IsTree) (k : Nat) {S : Finset V} (hS : S ∈ scopes G k)
    (u v : (S : Set V)) : (G.induce (S : Set V)).dist u v = G.dist u.val v.val := by
  obtain ⟨p,_,hp⟩ := ht.isConnected.exists_path_of_dist u.val v.val
  exact induceDist hp (scopeContainsPath ht k hS hp)

theorem scopeTree (ht : G.IsTree) (k : Nat) {S : Finset V} (hS : S ∈ scopes G k)
    (hne : S.Nonempty) : (G.induce (S : Set V)).IsTree := by
  obtain ⟨r,hr⟩ := hne
  letI : Nonempty (S : Set V) := ⟨⟨r,hr⟩⟩
  refine ⟨?_,ht.IsAcyclic.induce _⟩
  apply Connected.mk
  intro u v
  obtain ⟨p,_,hp⟩ := ht.isConnected.exists_path_of_dist u.val v.val
  exact (p.induce (S : Set V) (scopeContainsPath ht k hS hp)).reachable

theorem localSubview (ht : G.IsTree) (k : Nat) {S : Finset V} (hS : S ∈ scopes G k)
    (u : (S : Set V)) :
    (Finset.univ.filter fun v : (S : Set V) => (G.induce (S : Set V)).dist u v ≤ k).image
      Subtype.val = S ∩ ball G k u.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, ball]
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, by simpa [scopeDist ht k hS] using hw⟩
  · rintro ⟨hv, hv'⟩
    exact ⟨⟨v,hv⟩, by simpa [scopeDist ht k hS] using hv',rfl⟩

#print axioms fourPoint
#print axioms scopesCard
#print axioms localSubview
end TreeInfluence
