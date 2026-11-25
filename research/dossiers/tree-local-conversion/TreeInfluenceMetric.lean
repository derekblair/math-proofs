import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace TreeInfluence
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

theorem induceDist {S : Set V} {u v : S} {p : G.Walk u.val v.val}
    (hp : p.length = G.dist u.val v.val) (hS : ∀ x ∈ p.support, x ∈ S) :
    (G.induce S).dist u v = G.dist u.val v.val := by
  let q : (G.induce S).Walk u v := p.induce S hS
  have hq : q.length = p.length := by
    simpa [q] using (Walk.length_map (Embedding.induce S).toHom (p.induce S hS)).symm
  obtain ⟨r, hr⟩ := q.reachable.exists_walk_length_eq_dist
  have h₁ := (G.induce S).dist_le q
  have h₂ := G.dist_le (r.map (Embedding.induce S).toHom)
  rw [Walk.length_map, hr] at h₂
  change G.dist u.val v.val ≤ (G.induce S).dist u v at h₂
  exact le_antisymm (h₁.trans_eq (hq.trans hp)) h₂

theorem leafNotOnPath {l n a b : V} (hn : G.Adj l n)
    (hu : ∀ v, G.Adj l v → v = n) (ha : a ≠ l) (hb : b ≠ l)
    {p : G.Walk a b} (hp : p.IsPath) : l ∉ p.support := by
  intro hl
  obtain ⟨q,r,_,_,he⟩ := hp.mem_support_iff_exists_append.mp hl
  have hq := hu _ (q.adj_penultimate (Walk.not_nil_of_ne ha)).symm
  have hr := hu _ (r.adj_snd (Walk.not_nil_of_ne (Ne.symm hb)))
  have hq' : n ∈ q.support := hq ▸ q.getVert_mem_support (q.length - 1)
  have hr' : n ∈ r.support := hr ▸ r.getVert_mem_support 1
  exact (he ▸ hp).ne_of_mem_support_of_append hn.ne' hq' hr' rfl

theorem distDeleteLeaf (hc : G.Connected) {l n : V} (hn : G.Adj l n)
    (hu : ∀ v, G.Adj l v → v = n) (a b : ({l}ᶜ : Set V)) :
    (G.induce ({l}ᶜ : Set V)).dist a b = G.dist a.val b.val := by
  obtain ⟨p, hpath, hp⟩ := hc.exists_path_of_dist a.val b.val
  apply induceDist hp
  intro x hx
  change x ≠ l
  rintro rfl
  exact leafNotOnPath hn hu a.property b.property hpath hx

theorem leafDist (hc : G.Connected) {l n b : V} (hn : G.Adj l n)
    (hu : ∀ v, G.Adj l v → v = n) (hb : b ≠ l) :
    G.dist l b = G.dist n b + 1 := by
  have hupper := hc.dist_triangle (u := l) (v := n) (w := b)
  rw [dist_eq_one_iff_adj.mpr hn] at hupper
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist l b
  cases p with
  | nil => exact False.elim (hb rfl)
  | cons hed q =>
    have he := hu _ hed
    subst_vars
    have hlow := G.dist_le q
    simp only [Walk.length_cons] at hp
    omega

def FourPoint (G : SimpleGraph V) : Prop :=
  ∀ a b c x, G.dist a b + G.dist c x ≤
    max (G.dist a c + G.dist b x) (G.dist a x + G.dist b c)

theorem fourPointOfCard (m : Nat) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), Fintype.card V = m →
      G.IsTree → FourPoint G := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro V inst G hcard ht a b c x
    have hc := ht.isConnected
    by_cases hab : a = b
    · subst b
      have hh := hc.dist_triangle (u := c) (v := a) (w := x)
      rw [G.dist_comm (u := c) (v := a)] at hh
      simpa using hh.trans (le_max_left _ (G.dist a x + G.dist a c))
    by_cases hcx : c = x
    · subst x
      have hh := hc.dist_triangle (u := a) (v := c) (w := b)
      rw [G.dist_comm (u := c) (v := b)] at hh
      simpa using hh.trans (le_max_left _ (G.dist a c + G.dist b c))
    by_cases hac : a = c
    · subst c
      apply le_trans _ (le_max_right _ _)
      rw [G.dist_comm (u := b) (v := a), Nat.add_comm]
    by_cases hax : a = x
    · subst x
      rw [G.dist_comm (u := c) (v := a)]
      apply le_trans _ (le_max_left _ _)
      rw [G.dist_comm (u := b) (v := a), Nat.add_comm]
    by_cases hbc : b = c
    · subst c
      exact le_max_left _ _
    by_cases hbx : b = x
    · subst x
      rw [G.dist_comm (u := c) (v := b)]
      exact le_max_right _ _
    classical
    letI : Nontrivial V := ⟨⟨a,b,hab⟩⟩
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    obtain ⟨l, hl⟩ := ht.exists_vert_degree_one_of_nontrivial
    obtain ⟨n, hn, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
    let S := ({l}ᶜ : Set V)
    let H := G.induce S
    have hH : H.IsTree :=
      ⟨hc.induce_compl_singleton_of_degree_eq_one hl, ht.IsAcyclic.induce _⟩
    have hlt : Fintype.card S < m := by
      rw [← hcard]
      exact Fintype.card_subtype_lt (x := l) (by simp [S])
    have hh := ih (Fintype.card S) hlt H rfl hH
    let f (v : V) : S := if h : v = l then ⟨n, hn.ne'⟩ else ⟨v,h⟩
    let t (v : V) : Nat := if v = l then 1 else 0
    have eq (p q : V) (hpq : p ≠ q) :
        G.dist p q = H.dist (f p) (f q) + t p + t q := by
      rw [show H.dist (f p) (f q) = G.dist (f p).val (f q).val from
        distDeleteLeaf hc hn hu _ _]
      by_cases hp : p = l
      · subst p
        simp [f,t,hpq.symm,leafDist hc hn hu hpq.symm]
      · by_cases hq : q = l
        · subst q
          simp [f,t,hp,G.dist_comm (u := p) (v := l),leafDist hc hn hu hp,
            G.dist_comm (u := n) (v := p)]
        · simp [f,t,hp,hq]
    have hIH := hh (f a) (f b) (f c) (f x)
    rw [eq a b hab, eq c x hcx, eq a c hac, eq b x hbx, eq a x hax, eq b c hbc]
    rcases le_total (H.dist (f a) (f c) + H.dist (f b) (f x))
         (H.dist (f a) (f x) + H.dist (f b) (f c)) with h | h
    · rw [max_eq_right h] at hIH
      apply le_trans _ (le_max_right _ _)
      omega
    · rw [max_eq_left h] at hIH
      apply le_trans _ (le_max_left _ _)
      omega

theorem fourPoint [Fintype V] (ht : G.IsTree) : FourPoint G :=
  fourPointOfCard (Fintype.card V) G rfl ht
end TreeInfluence
