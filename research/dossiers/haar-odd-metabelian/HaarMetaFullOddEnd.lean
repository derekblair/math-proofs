import HaarMetaFullOdd
import HaarMetaPrimitiveDone
import HaarMetaFirstTorsion
import HaarMetaSecondTorsion

namespace HaarMetaFullOdd

open HaarMetaAlgebraCore HaarMetaEarlyCases HaarAllNoncommuting HaarClass4Generate
open HaarMetaSmallDispatchCore

universe u

private theorem second_solver : Solver.{u} (fun _ _ X Y => (Y * (X^2)⁻¹)^3 = 1) := by
  intro G Q _ _ _ _ odd f onto ab x y hx hy ne gen h
  apply HaarMetaSecondTorsion.cycle odd f onto ab x y hx hy ne gen
  · rw [sub_eq_add_neg]
    change (f y * ((f x)^(2:ℤ))⁻¹)^(3:ℕ) = 1
    simpa only [zpow_ofNat] using h
  · intro g X Y ha hX hY hn hg gx gy
    apply HaarMetaPrimitiveDone.p013 odd g (surj_one g X gx) ha X Y hX hY hn hg
    rw [gx, gy]
    change (3 : ZMod 15) = (3 : ℕ) • (1 : ZMod 15)
    simp [Nat.smul_one_eq_cast]
  · intro g X Y ha hX hY hn hg gx gy
    apply HaarMetaPrimitiveDone.p014 odd g (surj_one g X gx) ha X Y hX hY hn hg
    rw [gx, gy]
    change (4 : ZMod 15) = (4 : ℕ) • (1 : ZMod 15)
    simp [Nat.smul_one_eq_cast]

/-- The normalized Haar graph on a finite odd-order metabelian group with
distinct ports `1,x,y` contains a simple cycle of length 4, 8, 16 or 32. -/
theorem normalized {G : Type u} [Group G] [Finite G]
    (odd : Odd (Nat.card G)) (met : Meta G) (x y : G)
    (hx : x ≠ 1) (hy : y ≠ 1) (ne : x ≠ y) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  apply normalized_with
    (fun _ _ _ _ _ _ => HaarMetaPrimitiveDone.p013)
    (fun _ _ _ _ _ _ => HaarMetaPrimitiveDone.p014)
    (fun _ _ _ _ _ _ => HaarMetaPrimitiveDone.p025)
    (fun _ _ _ _ _ _ => HaarMetaFirstTorsion.first)
    second_solver odd met x y hx hy ne

/-- Every cubic Haar graph formed by three distinct ports in a finite metabelian
group of odd order has a simple cycle of length 4, 8, 16 or 32. -/
theorem arbitrary_three_ports {G : Type u} [Group G] [Finite G]
    (odd : Odd (Nat.card G)) (met : Meta G) (r s t : G)
    (hr : r ≠ s) (ht : r ≠ t) (hs : s ≠ t) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAnyPorts.HasPortCycle r s t n := by
  obtain ⟨hx,hy,ne⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨n,hn,hc⟩ := normalized odd met _ _ hx hy ne
  exact ⟨n,hn,HaarAnyPorts.map_cycle r s t hc⟩

end HaarMetaFullOdd

#print axioms HaarMetaFullOdd.normalized
#print axioms HaarMetaFullOdd.arbitrary_three_ports
