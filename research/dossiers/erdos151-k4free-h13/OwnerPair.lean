import OwnerTriangle

namespace Erdos151H13
open Erdős151 Erdos151H12
variable {V : Type*} [DecidableEq V] (G : V → V → Prop)

/-- If both owners of a double-lone column are marked, their two singleton
leaves must be joined by a lone edge. -/
theorem owner_pair_forces_lone
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S : Finset V) (f g a b z : V)
    (sf : f ∈ S) (sg : g ∈ S) (fg : f ≠ g)
    (na : a ∉ S) (nb : b ∉ S) (nz : z ∉ S)
    (ab : a ≠ b) (az : a ≠ z) (bz : b ≠ z)
    (fa : Lone G f a) (gb : Lone G g b) (fz : Lone G f z) (gz : Lone G g z)
    (sa : supported G S {f} a) (sb : supported G S {g} b)
    (sz : supported G S {f,g} z)
    (card : S.card = 12) (freeS : Free (Forbidden G) (S : Set V))
    (no : ∀ T : Finset V, 13 ≤ T.card → ¬ Free (Forbidden G) (T : Set V)) :
    Lone G a b := by
  let O : Finset V := {f,g}
  let R := S \ O
  let X : Finset V := {z}
  have hOS : O ⊆ S := by simp [O,Finset.insert_subset_iff,sf,sg]
  have hRS : R ⊆ S := Finset.sdiff_subset
  have hR : Free (Forbidden G) (R : Set V) :=
    fun U hU hs => freeS U hU (fun x hx => hRS (hs hx))
  have oc : O.card = 2 := by simp [O,fg,Finset.card_insert_of_notMem]
  have rc : R.card = 10 := by
    have h := Finset.card_sdiff_add_card_eq_card hOS
    change R.card + O.card = S.card at h
    omega
  have hdis : Disjoint X R := by
    apply Finset.disjoint_left.mpr
    intro w hw hr
    have e : w = z := by simpa [X] using hw
    subst w
    exact nz (hRS hr)
  have rt (q : V) (P : Finset V) (hP : P ⊆ O)
      (supp : supported G S P q) : ∀ w ∈ R, ¬ G q w := by
    intro w hw he
    exact (Finset.mem_sdiff.mp hw).2 (hP (supp w (hRS hw) he))
  have nota := rt a {f} (by simp [O]) sa
  have notb := rt b {g} (by simp [O]) sb
  have notz := rt z {f,g} (by simp [O]) sz
  refine force_lone_exchange G sym irr R X a b 13 hR ?_ ?_ ?_ ?_ ab ?_ ?_ ?_ no
  · intro u hu v hv
    have eu : u = z := by simpa [X] using hu
    have ev : v = z := by simpa [X] using hv
    subst u
    subst v
    exact irr _
  · intro w hw v hv
    have e : w = z := by simpa [X] using hw
    subst w
    exact notz v hv
  · intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · have e : w = z := by simpa [X] using hw
      subst w
      exact lone_neighbors_nonadjacent G sym fa fz.1
    · exact nota w hw
  · intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · have e : w = z := by simpa [X] using hw
      subst w
      exact lone_neighbors_nonadjacent G sym gb gz.1
    · exact notb w hw
  · simp [X,az,show a ∉ R from fun h => na (hRS h)]
  · simp [X,bz,show b ∉ R from fun h => nb (hRS h)]
  · rw [Finset.card_union_of_disjoint hdis, rc]
    simp [X]

#print axioms owner_pair_forces_lone
end Erdos151H13
