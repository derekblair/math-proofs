import UnblockingGraph
import RamseySmall

namespace Erdos151H12
open Erdős151

variable {V : Type*} (G : V → V → Prop)

theorem lone_symm (hs : ∀ {a b}, G a b → G b a) {u v : V} (h : Lone G u v) :
    Lone G v u := ⟨hs h.1, fun x e => h.2 x ⟨e.2,e.1⟩⟩

theorem safe_insert_one (hs : ∀ {a b}, G a b → G b a) (hir : ∀ a, ¬ G a a)
    (T : Set V) (u : V) (hT : Free (Forbidden G) T)
    (hl : ∀ a ∈ T, ¬ Lone G u a)
    (ht : ∀ a ∈ T, ∀ b ∈ T, G u a → G u b → ¬ G a b) :
    Free (Forbidden G) (insert u T) := by
  intro A hA hsub
  rcases hA with ⟨a,b,rfl,hab⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
  · have ha : a = u ∨ a ∈ T := Set.mem_insert_iff.mp (hsub (by simp))
    have hb : b = u ∨ b ∈ T := Set.mem_insert_iff.mp (hsub (by simp))
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hir _ hab.1
    · exact hl _ hb hab
    · exact hl _ ha (lone_symm G hs hab)
    · exact hT _ (Or.inl ⟨a,b,rfl,hab⟩) (by simpa [Set.insert_subset_iff, ha, hb])
  · have ha : a = u ∨ a ∈ T := Set.mem_insert_iff.mp (hsub (by simp))
    have hb : b = u ∨ b ∈ T := Set.mem_insert_iff.mp (hsub (by simp))
    have hc : c = u ∨ c ∈ T := Set.mem_insert_iff.mp (hsub (by simp))
    rcases ha with rfl | ha <;> rcases hb with rfl | hb <;> rcases hc with rfl | hc
    · exact hir _ hab
    · exact hir _ hab
    · exact hir _ hac
    · exact ht b hb c hc hab hac hbc
    · exact hir _ hbc
    · exact ht a ha c hc (hs hab) hbc hac
    · exact ht a ha b hb (hs hac) (hs hbc) hab
    · exact hT _ (Or.inr ⟨a,b,c,rfl,hab,hbc,hac⟩)
        (by simpa [Set.insert_subset_iff, ha, hb, hc])

/-- Both adjacent (non-lone) and nonadjacent hub insertions. Conditions only concern
ambient blockers and are inherited by all subsets of the chosen residual universe. -/
theorem safe_insert_two (hs : ∀ {a b}, G a b → G b a) (hir : ∀ a, ¬ G a a)
    (T : Set V) (u v : V) (hT : Free (Forbidden G) T)
    (hne : ¬ Lone G u v)
    (hl : ∀ a ∈ T, ¬ Lone G u a ∧ ¬ Lone G v a)
    (ht : ∀ w, w = u ∨ w = v → ∀ a ∈ T, ∀ b ∈ T, G w a → G w b → ¬ G a b)
    (hc : ∀ a ∈ T, G u v → G u a → ¬ G v a) :
    Free (Forbidden G) (insert u (insert v T)) := by
  have hv := safe_insert_one G hs hir T v hT (fun a ha => (hl a ha).2) (ht v (Or.inr rfl))
  apply safe_insert_one G hs hir (insert v T) u hv
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hne
    · exact (hl a ha).1
  · intro a ha b hb hua hub hab
    rcases Set.mem_insert_iff.mp ha with rfl | haT <;> rcases Set.mem_insert_iff.mp hb with rfl | hbT
    · exact hir _ hab
    · exact hc b hbT hua hub hab
    · exact hc a haT hub hua (hs hab)
    · exact ht u (Or.inl rfl) a haT b hbT hua hub hab

/-- The two-neighborhood nonadjacent conflict graph is triangle-free. -/
def pairConflict (u v a b : V) : Prop :=
  G a b ∧ ((G u a ∧ G u b) ∨ (G v a ∧ G v b))

theorem pairConflict_triangleFree (u v : V) (hl : TriangleFreeLinks G) :
    Erdos151Ramsey.TriangleFree (pairConflict G u v) := by
  intro a b c hab hbc hac
  rcases hab.2 with h1 | h1 <;> rcases hbc.2 with h2 | h2 <;> rcases hac.2 with h3 | h3
  · exact hl u a b c h1.1 h1.2 h2.2 hab.1 hbc.1 hac.1
  · exact hl u a b c h1.1 h1.2 h2.2 hab.1 hbc.1 hac.1
  · exact hl u a b c h1.1 h1.2 h3.2 hab.1 hbc.1 hac.1
  · exact hl v a b c h3.1 h2.1 h2.2 hab.1 hbc.1 hac.1
  · exact hl u a b c h3.1 h2.1 h2.2 hab.1 hbc.1 hac.1
  · exact hl v a b c h1.1 h1.2 h3.2 hab.1 hbc.1 hac.1
  · exact hl v a b c h1.1 h1.2 h2.2 hab.1 hbc.1 hac.1
  · exact hl v a b c h1.1 h1.2 h2.2 hab.1 hbc.1 hac.1

#print axioms safe_insert_two
#print axioms pairConflict_triangleFree
end Erdos151H12
