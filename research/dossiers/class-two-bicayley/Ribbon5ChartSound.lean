import Ribbon5BridgeChart
import HaarBound16

namespace Ribbon5Bridge

variable {G : Type*} [Group G]

def action (x y : G) (s : Bool × G) (p : P) : Bool × G :=
  if p=2 then (!s.1,s.2) else
    (s.1,s.2*(if s.1 then (if p=0 then y else y⁻¹)
                         else (if p=0 then x else x⁻¹)))

def vert (x y c : G) (s : Q) : Bool × G := (s.1,HaarCycle.norm x y c s.2)

theorem move (x y c : G) (cx : Commute c x) (cy : Commute c y)
    (xy : x*y=y*x*c) (q : Q) (p : P) :
    vert x y c (push q p) = action x y (vert x y c q) p := by
  obtain ⟨b,⟨i,j,k⟩⟩ := q
  have xpos := HaarCycle.normX x y c cx (i,j,k)
  have ypos := HaarCycle.normY x y c cx cy xy (i,j,k)
  have xn := HaarCycle.normX x y c cx (i-1,j,k)
  have yn := HaarCycle.normY x y c cx cy xy (i,j-1,k-i)
  have X : HaarCycle.rightX (i-1,j,k)=(i,j,k) := by simp [HaarCycle.rightX]
  have Y : HaarCycle.rightY (i,j-1,k-i)=(i,j,k) := by simp [HaarCycle.rightY]
  rw [X] at xn
  rw [Y] at yn
  have xn' := congrArg (·*x⁻¹) xn
  have yn' := congrArg (·*y⁻¹) yn
  cases b <;> fin_cases p <;> simp [vert,action,push]
  · exact xpos
  · simpa [mul_assoc] using xn'.symm
  · exact ypos
  · simpa [mul_assoc] using yn'.symm

theorem action_adj (x y : G) (s : Bool × G) (p : P) :
    Ribbon.Adj x y s (action x y s p) := by
  obtain ⟨b,g⟩ := s
  cases b <;> fin_cases p <;> simp [Ribbon.Adj,action, mul_assoc]

theorem map_action {H : Type*} [Group H] (f : G →* H) (x y : G)
    (s : Bool × G) (p : P) :
    (fun u : Bool × G => (u.1,f u.2)) (action x y s p) =
      action (f x) (f y) (s.1,f s.2) p := by
  obtain ⟨b,g⟩ := s
  cases b <;> fin_cases p <;> simp [action]

private theorem power_gap (c : G) (h : ∀ k : Nat, 1≤k → k≤4 → c^k≠1)
    (a b : ℤ) (g : gap (a-b)) : c^a≠c^b := by
  intro eq
  have E : c^(a-b)=1 := by rw [zpow_sub,eq,mul_inv_cancel]
  rcases g with d|d|d|d|d|d|d|d <;>
    rw [d] at E <;>
    norm_num [zpow_neg] at E <;>
    first | exact h 1 (by decide) (by decide) (by simpa only [pow_one] using E)
          | exact h 2 (by decide) (by decide) E
          | exact h 3 (by decide) (by decide) E
          | exact h 4 (by decide) (by decide) E

theorem separates_low (x y c : G) (cx : Commute c x) (cy : Commute c y)
    (xy : x*y=y*x*c) (good : ∀ k : Nat, 1≤k → k≤4 → c^k≠1)
    (u v : Q) (sv : separated u v) : vert x y c u ≠ vert x y c v := by
  intro e
  have E : HaarCycle.norm x y c u.2=HaarCycle.norm x y c v.2 := congrArg Prod.snd e
  have K := HaarBound16.conjugate_eq x y c cx cy xy E
  rcases sv with h|h|h|⟨hi,hj,h⟩
  · exact h (congrArg (Prod.fst : Bool × G → Bool) e)
  · exact power_gap c good _ _ h K.1
  · exact power_gap c good _ _ h K.2
  · unfold HaarCycle.norm at E
    rw [hi,hj] at E
    exact power_gap c good _ _ h (mul_left_cancel E)

end Ribbon5Bridge
#print axioms Ribbon5Bridge.move
#print axioms Ribbon5Bridge.separates_low
