import Small269

open SimpleGraph
open scoped BigOperators
namespace Refute269

abbrev Big := Vert 35 62
abbrev G := graph 35 62

def ia : Big → Fin 35
  | .inr (.inl (i,_)) => i
  | _ => 0
def ib : Big → Fin 62
  | .inr (.inr (i,_)) => i
  | _ => 0

def project (a : Fin 35) (b : Fin 62) : G →g graph 2 2 := reindex (color a) (color b)
def lift (a a' : Fin 35) (b b' : Fin 62) : graph 2 2 →g G := reindex (pick a a') (pick b b')

def down (v : Big) : G →g graph 2 2 := project (ia v) (ib v)
def up (v w : Big) : graph 2 2 →g G := lift (ia v) (ia w) (ib v) (ib w)

lemma updown_left (v w : Big) : up v w (down v v) = v := by
  rcases v with p | (⟨i,r⟩ | ⟨i,r⟩)
  · rfl
  · change A (pick i (ia w) (color i i)) r = A i r
    rw [pick_anchor]
  · change B (pick i (ib w) (color i i)) r = B i r
    rw [pick_anchor]

lemma updown_right (v w : Big) : up v w (down v w) = w := by
  rcases w with p | (⟨i,r⟩ | ⟨i,r⟩)
  · rfl
  · change A (pick (ia v) i (color (ia v) i)) r = A i r
    rw [pick_other]
  · change B (pick (ib v) i (color (ib v) i)) r = B i r
    rw [pick_other]

def value (v w : Big) : ℕ := dd (down v v) (down v w)

lemma hasWalk (v w : Big) : ∃ p : G.Walk v w, p.length = value v w := by
  obtain ⟨p,hp⟩ := walks (down v v) (down v w)
  have hmap : ∃ q : G.Walk (up v w (down v v)) (up v w (down v w)), q.length = value v w := by
    exact ⟨p.map (up v w), (Walk.length_map _ _).trans hp⟩
  rw [updown_left, updown_right] at hmap
  exact hmap

lemma conn : G.Connected := by
  refine { preconnected := ?_, nonempty := ⟨P 0⟩ }
  intro v w
  obtain ⟨p,_⟩ := hasWalk v w
  exact ⟨p⟩

lemma dist_value (v w : Big) : G.dist v w = value v w := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := hasWalk v w
    exact (dist_le p).trans_eq hp
  · obtain ⟨p,hp⟩ := conn.exists_walk_length_eq_dist v w
    have hd := dist_le (p.map (down v))
    rw [exact_dist, Walk.length_map, hp] at hd
    exact hd

def other {m : Nat} [NeZero m] (i : Fin m) : Fin m := if i = 0 then Fin.ofNat m 1 else 0

lemma otherA (a : Fin 35) : other a ≠ a := by
  unfold other
  by_cases h : a = 0
  · simp [h]
  · simp [h, Ne.symm h]

lemma otherB (b : Fin 62) : other b ≠ b := by
  unfold other
  by_cases h : b = 0
  · simp [h]
  · simp [h, Ne.symm h]

lemma color_pick {m : Nat} {a b : Fin m} (h : b ≠ a) (x : Fin 2) :
    color a (pick a b x) = x := by
  fin_cases x <;> simp [color,pick,h]

lemma rever (v : Big) (w : Small) :
    down v (lift (ia v) (other (ia v)) (ib v) (other (ib v)) w) = w := by
  rcases w with p | (⟨i,r⟩ | ⟨i,r⟩)
  · rfl
  · change A (color (ia v) (pick (ia v) (other (ia v)) i)) r = A i r
    rw [color_pick (otherA _)]
  · change B (color (ib v) (pick (ib v) (other (ib v)) i)) r = B i r
    rw [color_pick (otherB _)]

lemma hasDistFour (v : Big) : ∃ w, G.dist v w = 4 := by
  obtain ⟨w,hw⟩ := has4 (down v v)
  refine ⟨lift (ia v) (other (ia v)) (ib v) (other (ib v)) w, ?_⟩
  rw [dist_value]
  unfold value
  rwa [rever]

lemma ecc (v : Big) : G.eccent v = 4 := by
  apply le_antisymm
  · apply iSup_le
    intro w
    rw [← (conn v w).coe_dist_eq_edist, dist_value]
    exact_mod_cast max4 (down v v) (down v w)
  · obtain ⟨w,hw⟩ := hasDistFour v
    have h := G.edist_le_eccent (u := v) (v := w)
    rwa [← (conn v w).coe_dist_eq_edist, hw] at h

lemma rad : G.radius = 4 := by
  simp [SimpleGraph.radius, ecc]

lemma center_all (v : Big) : v ∈ G.center := by
  rw [G.mem_center_iff, ecc, rad]

#print axioms center_all
end Refute269
