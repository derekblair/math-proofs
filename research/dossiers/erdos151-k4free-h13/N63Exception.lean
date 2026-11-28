import N63TableCore
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def common83 : List Nat := [2,3,4,5]
def common88 : List Nat := [0,1,2,3]

def chooseCenters (rows : Array Nat) (x y : Nat) : List Nat :=
  let pool := (List.range 9).filter fun z =>
    z != x && z != y && !adj rows x z && !adj rows y z
  ((pool.flatMap fun a => pool.filterMap fun b =>
    if a < b && !adj rows a b then some [a,b] else none).head?).getD []

theorem exception83_centers :
    ∀ x ∈ common83, ∀ y ∈ common83, x ≠ y →
      pivotOK chart83 9 x y (chooseCenters chart83 x y) ∧
        (chooseCenters chart83 x y).length = 2 := by decide +kernel

theorem exception88_centers :
    ∀ x ∈ common88, ∀ y ∈ common88, x ≠ y →
      pivotOK chart88 9 x y (chooseCenters chart88 x y) ∧
        (chooseCenters chart88 x y).length = 2 := by decide +kernel

theorem exceptional_budget :
    ∀ a b : Fin 4, ∀ s : Fin 13,
      (a.val ≠ 0 ∨ b.val ≠ 0 ∨ s.val ≠ 0) →
      17 ≤ 4+(3+a.val)+(3+b.val)+s.val+2+
        outerFloor (3+a.val) (3+b.val) s.val := by decide +kernel

theorem exceptional_budget_transfer (a b s : Nat)
    (ha : 3 ≤ a) (ha' : a ≤ 6) (hb : 3 ≤ b) (hb' : b ≤ 6) (hs : s ≤ 12)
    (h : a ≠ 3 ∨ b ≠ 3 ∨ s ≠ 0) :
    17 ≤ 4+a+b+s+2+outerFloor a b s := by
  have h := exceptional_budget ⟨a-3,by omega⟩ ⟨b-3,by omega⟩ ⟨s,by omega⟩ (by
    change a-3 ≠ 0 ∨ b-3 ≠ 0 ∨ s ≠ 0
    omega)
  change 17 ≤ 4+(3+(a-3))+(3+(b-3))+s+2+outerFloor (3+(a-3)) (3+(b-3)) s at h
  simpa only [Nat.add_sub_of_le ha, Nat.add_sub_of_le hb] using h

#print axioms exception83_centers
#print axioms exception88_centers
#print axioms exceptional_budget_transfer
end Erdos151N63
