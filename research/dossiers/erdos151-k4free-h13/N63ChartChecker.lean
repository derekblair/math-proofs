import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

namespace Erdos151N63
def mask (rows : Array Nat) (i : Nat) : Nat := rows[i]?.getD 0
def adj (rows : Array Nat) (i j : Nat) : Bool := (mask rows i).testBit j
def deg (rows : Array Nat) (n i : Nat) : Nat := ((List.range n).filter (adj rows i)).length

def alphaFloor (n : Nat) : Nat :=
  if 9 ≤ n then 4 else if 6 ≤ n then 3 else if 3 ≤ n then 2 else if 1 ≤ n then 1 else 0

def outerFloor (a b s : Nat) : Nat :=
  max (alphaFloor (14-a-b-s)) <|
    max (alphaFloor (7-a-s)+alphaFloor (7-b-s))
      (if s=1 ∧ a≤4 ∧ b≤4 then 3 else 0)

def priceOK (n dx dy m : Nat) : Prop :=
  ∀ i : Fin (13-n), ∀ j : Fin (13-n), ∀ s : Fin 13,
    17 ≤ 4 + (dx+i.val) + (dy+j.val) + s.val + m +
      outerFloor (dx+i.val) (dy+j.val) s.val

def pivotOK (rows : Array Nat) (n x y : Nat) (S : List Nat) : Prop :=
  x < n ∧ y < n ∧ x ≠ y ∧ adj rows x y = false ∧
  S.Nodup ∧
  (∀ z ∈ S, z < n ∧ z ≠ x ∧ z ≠ y ∧ adj rows x z = false ∧ adj rows y z = false) ∧
  (∀ u ∈ S, ∀ v ∈ S, adj rows u v = false)

theorem price_transfer (n dx dy m c1 c2 s : Nat)
    (h : priceOK n dx dy m) (hx : dx ≤ c1) (hy : dy ≤ c2)
    (hX : c1 ≤ dx + (12-n)) (hY : c2 ≤ dy + (12-n))
    (hs : s ≤ 12) (hn : n ≤ 12) :
    17 ≤ 4+c1+c2+s+m+outerFloor c1 c2 s := by
  have h := h ⟨c1-dx,by omega⟩ ⟨c2-dy,by omega⟩ ⟨s,by omega⟩
  change 17 ≤ 4 + (dx+(c1-dx)) +(dy+(c2-dy))+s+m+
    outerFloor (dx+(c1-dx)) (dy+(c2-dy)) s at h
  simpa only [Nat.add_sub_of_le hx, Nat.add_sub_of_le hy] using h

def chart83 : Array Nat := #[112, 176, 448, 448, 259, 259, 13, 14, 60]
def chart88 : Array Nat := #[112, 336, 224, 448, 131, 261, 15, 28, 42]

def relabelOK (rows target : Array Nat) (n : Nat) (perm : Fin n → Fin n) : Prop :=
  Function.Injective perm ∧
  ∀ i j : Fin n, adj rows i.val j.val = adj target (perm i).val (perm j).val

#print axioms price_transfer
end Erdos151N63
