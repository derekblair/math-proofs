import Degree10Unblocking

namespace Erdős151

variable {V : Type*}

def Lone (G : V → V → Prop) (a b : V) : Prop :=
  G a b ∧ ∀ x, ¬ (G a x ∧ G b x)

def Forbidden (G : V → V → Prop) (S : Set V) : Prop :=
  (∃ a b, S = {a, b} ∧ Lone G a b) ∨
  (∃ a b c, S = {a, b, c} ∧ G a b ∧ G b c ∧ G a c)

/-- K4-free expressed without repeated-vertex side conditions:
under a loopless relation this rules out exactly triangles in links. -/
def TriangleFreeLinks (G : V → V → Prop) : Prop :=
  ∀ w a b c, G w a → G w b → G w c → G a b → G b c → ¬ G a c

theorem forbidden_clique (G : V → V → Prop)
    (hsym : ∀ {a b}, G a b → G b a)
    (S : Set V) (hS : Forbidden G S) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (hne : u ≠ v) : G u v := by
  rcases hS with ⟨a,b,rfl,hab,_⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> first
      | exact False.elim (hne rfl)
      | exact hab
      | exact hsym hab
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl <;> first
      | exact False.elim (hne rfl)
      | exact hab
      | exact hbc
      | exact hac
      | exact hsym hab
      | exact hsym hbc
      | exact hsym hac

theorem neighborhood_free (G : V → V → Prop)
    (hsym : ∀ {a b}, G a b → G b a) (hlink : TriangleFreeLinks G)
    (w : V) : Free (Forbidden G) {v | G w v} := by
  intro S hS hN
  rcases hS with ⟨a,b,rfl,_,hl⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
  · exact hl w ⟨hsym (hN (by simp)), hsym (hN (by simp))⟩
  · exact hlink w a b c (hN (by simp)) (hN (by simp)) (hN (by simp)) hab hbc hac

def RedPlus (G : V → V → Prop) (color : V → V → Bool) (a b : V) : Prop :=
  G a b ∧ (color a b = true ∨ Lone G a b)

theorem redPlus_triangleFree (G : V → V → Prop) (color : V → V → Bool)
    (hsym : ∀ {a b}, G a b → G b a)
    (valid : ∀ a b c, G a b → G b c → G a c →
      ¬ (color a b = color b c ∧ color a b = color a c))
    (a b c : V) (hab : RedPlus G color a b)
    (hbc : RedPlus G color b c) (hac : RedPlus G color a c) : False := by
  have h1 : color a b = true := by
    rcases hab.2 with h|h
    · exact h
    · exact False.elim (h.2 c ⟨hac.1,hbc.1⟩)
  have h2 : color b c = true := by
    rcases hbc.2 with h|h
    · exact h
    · exact False.elim (h.2 a ⟨hsym hab.1,hsym hac.1⟩)
  have h3 : color a c = true := by
    rcases hac.2 with h|h
    · exact h
    · exact False.elim (h.2 b ⟨hab.1,hsym hbc.1⟩)
  exact valid a b c hab.1 hbc.1 hac.1 ⟨h1.trans h2.symm,h1.trans h3.symm⟩

theorem independent_redPlus_free (G : V → V → Prop) (color : V → V → Bool)
    (valid : ∀ a b c, G a b → G b c → G a c →
      ¬ (color a b = color b c ∧ color a b = color a c)) (S : Set V)
    (hi : ∀ a ∈ S, ∀ b ∈ S, ¬ RedPlus G color a b) :
    Free (Forbidden G) S := by
  intro Z hZ hS
  rcases hZ with ⟨a,b,rfl,hl⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
  · exact hi a (hS (by simp)) b (hS (by simp)) ⟨hl.1,Or.inr hl⟩
  · have h1 : color a b = false := by
      cases he : color a b
      · rfl
      · exact False.elim (hi a (hS (by simp)) b (hS (by simp)) ⟨hab,Or.inl he⟩)
    have h2 : color b c = false := by
      cases he : color b c
      · rfl
      · exact False.elim (hi b (hS (by simp)) c (hS (by simp)) ⟨hbc,Or.inl he⟩)
    have h3 : color a c = false := by
      cases he : color a c
      · rfl
      · exact False.elim (hi a (hS (by simp)) c (hS (by simp)) ⟨hac,Or.inl he⟩)
    exact valid a b c hab hbc hac ⟨h1.trans h2.symm,h1.trans h3.symm⟩

#print axioms forbidden_clique
#print axioms neighborhood_free
#print axioms redPlus_triangleFree
#print axioms independent_redPlus_free
end Erdős151
