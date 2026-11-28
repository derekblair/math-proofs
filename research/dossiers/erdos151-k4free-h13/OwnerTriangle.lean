import OwnerExchange
import Mathlib.Data.Finset.SDiff

namespace Erdos151H13
open Erdős151 Erdos151H12
variable {V : Type*} [DecidableEq V] (G : V → V → Prop)

def supported (S O : Finset V) (x : V) : Prop := ∀ a ∈ S, G x a → a ∈ O

/-- Three double-lone columns of an owner triangle and the leaf of a
marked corner yield a four-for-three swap unless the opposite column
is a lone neighbor of that corner's leaf. The other two owners need
not themselves be marked. -/
theorem owner_triangle_forces_lone
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S : Finset V) (f g h x y z a : V)
    (sf : f ∈ S) (sg : g ∈ S) (sh : h ∈ S)
    (fg : f ≠ g) (fh : f ≠ h) (gh : g ≠ h)
    (nx : x ∉ S) (ny : y ∉ S) (nz : z ∉ S) (na : a ∉ S)
    (xy : x ≠ y) (ax : a ≠ x) (ay : a ≠ y)
    (zx : z ≠ x) (zy : z ≠ y) (az : a ≠ z)
    (fx : Lone G f x) (gx : Lone G g x)
    (fy : Lone G f y) (hy : Lone G h y)
    (gz : Lone G g z) (hz : Lone G h z) (fa : Lone G f a)
    (sx : supported G S {f,g} x) (sy : supported G S {f,h} y)
    (sz : supported G S {g,h} z) (sa : supported G S {f} a)
    (card : S.card = 12) (freeS : Free (Forbidden G) (S : Set V))
    (no : ∀ T : Finset V, 13 ≤ T.card → ¬ Free (Forbidden G) (T : Set V)) :
    Lone G a z := by
  let O : Finset V := {f,g,h}
  let R := S \ O
  let X : Finset V := {x,y}
  have hOS : O ⊆ S := by simp [O, Finset.insert_subset_iff, sf,sg,sh]
  have hRS : R ⊆ S := Finset.sdiff_subset
  have hR : Free (Forbidden G) (R : Set V) :=
    fun U hU hsub => freeS U hU (fun b hb => hRS (hsub hb))
  have oc : O.card = 3 := by simp [O, fg,fh,gh,Finset.card_insert_of_notMem]
  have rc : R.card = 9 := by
    have h := Finset.card_sdiff_add_card_eq_card hOS
    change R.card + O.card = S.card at h
    omega
  have xc : X.card = 2 := by simp [X,xy,Finset.card_insert_of_notMem]
  have hdisj : Disjoint X R := by
    apply Finset.disjoint_left.mpr
    intro w hw hr
    change w ∈ ({x,y} : Finset V) at hw
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hw : w=x ∨ w=y) with rfl|rfl
    · exact nx (hRS hr)
    · exact ny (hRS hr)
  have rt (q : V) (P : Finset V) (hP : P ⊆ O)
      (supp : supported G S P q) : ∀ w ∈ R, ¬ G q w := by
    intro w hw hw'
    exact (Finset.mem_sdiff.mp hw).2 (hP (supp w (hRS hw) hw'))
  have notx := rt x {f,g} (by simp [O,Finset.insert_subset_iff]) sx
  have noty := rt y {f,h} (by simp [O,Finset.insert_subset_iff]) sy
  have notz := rt z {g,h} (by simp [O,Finset.insert_subset_iff]) sz
  have nota := rt a {f} (by simp [O,Finset.insert_subset_iff]) sa
  have nxy := lone_neighbors_nonadjacent G sym fx fy.1
  have nax := lone_neighbors_nonadjacent G sym fa fx.1
  have nay := lone_neighbors_nonadjacent G sym fa fy.1
  have nzx := lone_neighbors_nonadjacent G sym gz gx.1
  have nzy := lone_neighbors_nonadjacent G sym hz hy.1
  refine force_lone_exchange G sym irr R X a z 13 hR ?_ ?_ ?_ ?_ az ?_ ?_ ?_ no
  · intro w hw b hb
    simp only [X,Finset.mem_insert,Finset.mem_singleton] at hw hb
    rcases hw with rfl|rfl <;> rcases hb with rfl|rfl
    · exact irr _
    · exact nxy
    · exact fun h => nxy (sym h)
    · exact irr _
  · intro w hw b hb
    simp only [X,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl|rfl
    · exact notx b hb
    · exact noty b hb
  · intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · simp only [X,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl|rfl
      · exact nax
      · exact nay
    · exact nota w hw
  · intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · simp only [X,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl|rfl
      · exact nzx
      · exact nzy
    · exact notz w hw
  · simp only [Finset.mem_union, X, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨ax,ay⟩, fun h => na (hRS h)⟩
  · simp only [Finset.mem_union, X, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨zx,zy⟩, fun h => nz (hRS h)⟩
  · rw [Finset.card_union_of_disjoint hdisj, xc, rc]

#print axioms owner_triangle_forces_lone
end Erdos151H13
