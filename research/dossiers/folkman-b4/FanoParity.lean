import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace FolkmanB4
open scoped BigOperators

def even (a b c : Bool) : Bool := !(Bool.xor (Bool.xor a b) c)

def mass (a b c d e f g : Bool) : Nat :=
  a.toNat+b.toNat+c.toNat+d.toNat+e.toNat+f.toNat+g.toNat

theorem line_row : ∀ a b c d e f g : Bool,
    (even a d e && even a f g && even b d f &&
      even b e g && even c d g && even c e f) = true →
    4 ∣ mass a b c d e f g := by decide

theorem point_row : ∀ a b c d e f g : Bool,
    (even a b c && even a d e && even b d f &&
      even c e f && even a f g) = true →
    4 ∣ mass a b c d e f g := by decide

def Row (V : Type*) := Fin 7 → V → Bool

/-- All columns model graph edges, so every column has two endpoints. -/
def EdgeWeights {V : Type*} [Fintype V] (p : Row V) : Prop :=
  ∀ i, (∑ v, (p i v).toNat) = 2

theorem row_impossible {V : Type*} [Fintype V] (p : Row V) (h : EdgeWeights p)
    (P : ∀ v : V, 4 ∣ ∑ i, (p i v).toNat) : False := by
  have H : 4 ∣ ∑ v : V, ∑ i : Fin 7, (p i v).toNat := Finset.dvd_sum fun v _ => P v
  rw [Finset.sum_comm] at H
  have hc (i : Fin 7) : (∑ v : V, (p i v).toNat)=2 := h i
  simp only [hc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
  omega

theorem mass_eq_sum {V : Type*} (p : Row V) (v : V) :
    (∑ i, (p i v).toNat) = mass (p 0 v) (p 1 v) (p 2 v) (p 3 v)
      (p 4 v) (p 5 v) (p 6 v) := by
  simp [Fin.sum_univ_succ,mass,Nat.add_assoc]

/-- A Fano plane minus a line cannot be realized by graph edges and triangles.
Only the edge weights and parity equations are needed. -/
theorem deleted_line_impossible {V : Type*} [Fintype V] (p : Row V) (h : EdgeWeights p)
    (e : ∀ v, (even (p 0 v) (p 3 v) (p 4 v) && even (p 0 v) (p 5 v) (p 6 v) &&
      even (p 1 v) (p 3 v) (p 5 v) && even (p 1 v) (p 4 v) (p 6 v) &&
      even (p 2 v) (p 3 v) (p 6 v) && even (p 2 v) (p 4 v) (p 5 v))=true) : False := by
  apply row_impossible p h
  intro v
  rw [mass_eq_sum]
  exact line_row _ _ _ _ _ _ _ (e v)

/-- A Fano plane minus a point with just one dangling line completed by an
arbitrary graph edge also cannot occur. Column six now denotes the external
edge of that line; the other two dangling lines are not assumed. -/
theorem deleted_point_impossible {V : Type*} [Fintype V] (p : Row V) (h : EdgeWeights p)
    (e : ∀ v, (even (p 0 v) (p 1 v) (p 2 v) && even (p 0 v) (p 3 v) (p 4 v) &&
      even (p 1 v) (p 3 v) (p 5 v) && even (p 2 v) (p 4 v) (p 5 v) &&
      even (p 0 v) (p 5 v) (p 6 v))=true) : False := by
  apply row_impossible p h
  intro v
  rw [mass_eq_sum]
  exact point_row _ _ _ _ _ _ _ (e v)

#print axioms deleted_line_impossible
#print axioms deleted_point_impossible
end FolkmanB4
