import HaarMetaEarlyCases
import HaarMetaPermute
import HaarHoneyHaar

namespace HaarMetaFullOdd

open HaarMetaAlgebraCore HaarMetaEarlyCases HaarClass4Generate HaarAllNoncommuting

universe u

/-- Remaining normal-form solvers all use this finite, odd-order extension setup. -/
abbrev Solver (rel : ∀ (Q : Type u) [CommGroup Q], Q → Q → Prop) :=
  ∀ (G Q : Type u) [Group G] [CommGroup Q] [Finite G] [Finite Q],
    Odd (Nat.card G) → ∀ (f : G →* Q), Function.Surjective f →
      (∀ a b : f.ker, a*b=b*a) →
      ∀ (x y : G), x ≠ 1 → y ≠ 1 → x ≠ y → Generates x y →
        rel Q (f x) (f y) → Good x y

/-- Assembly of the locally injective honeycomb and short-relation normal forms. -/
theorem extension_with {G Q : Type u} [Group G] [CommGroup Q] [Finite G]
    (p013 : Solver.{u} (fun _ _ X Y => Y = X^3))
    (p014 : Solver.{u} (fun _ _ X Y => Y = X^4))
    (p025 : Solver.{u} (fun _ _ X Y => X^5 = Y^2))
    (first : Solver.{u} (fun _ _ X _ => X^3 = 1))
    (second : Solver.{u} (fun _ _ X Y => (Y * (X^2)⁻¹)^3 = 1))
    (odd : Odd (Nat.card G)) (f : G →* Q) (onto : Function.Surjective f)
    (ab : ∀ a b : f.ker, a*b=b*a) (x y : G)
    (hx : x ≠ 1) (hy : y ≠ 1) (ne : x ≠ y) (gen : Generates x y) : Good x y := by
  classical
  let : Finite Q := Finite.of_surjective f onto
  by_cases hh : HaarHoneyHaar.noShort (f x) (f y)
  · let : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
    obtain ⟨n,hn,hc⟩ := HaarHoneyHaar.odd_no_short f x y (mul_comm _ _) odd hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact ⟨16, by decide, hc⟩
    · exact ⟨32, by decide, hc⟩
  · unfold HaarHoneyHaar.noShort at hh
    push Not at hh
    obtain ⟨i,j,hi,hj,h,hij⟩ := hh
    have h₂ (z : Additive Q) (hz : (2 : ℤ) • z = 0) : z = 0 := by
      have oQ : Odd (Nat.card Q) := odd_of_surj f onto odd
      apply no_two_fin_odd (A := Additive Q) oQ
      simpa [two_zsmul] using hz
    have hab : i • HaarMetaPermute.image f x + j • HaarMetaPermute.image f y = 0 := h
    have hij' : i ≠ 0 ∨ j ≠ 0 := by
      by_cases hi0 : i = 0
      · exact Or.inr (hij hi0)
      · exact Or.inl hi0
    obtain ⟨σ, forms, ⟨hX,hY,hne⟩, tr⟩ :=
      HaarMetaPermute.normalize f x y hx hy ne h₂ i j (by omega) (by omega) hij' hab
    let X := HaarMetaPermute.ports x y (σ 1) * (HaarMetaPermute.ports x y (σ 0))⁻¹
    let Y := HaarMetaPermute.ports x y (σ 2) * (HaarMetaPermute.ports x y (σ 0))⁻¹
    have newGen : Generates X Y := HaarMetaPermute.normalized_generates x y σ gen
    have newGood : Good X Y := by
      change HaarMetaShortRelations.NormalForm (HaarMetaPermute.image f X) (HaarMetaPermute.image f Y) at forms
      rcases forms with c | c | c | c | c | c | c
      · exact collapse odd f ab X Y hX hY hne c
      · apply ap odd f onto ab X Y hX hY hne newGen
        change f Y = (f X)^(2:ℤ) at c
        simpa only [zpow_ofNat] using c
      · apply p013 G Q odd f onto ab X Y hX hY hne newGen
        change f Y = (f X)^(3:ℤ) at c
        simpa only [zpow_ofNat] using c
      · apply p014 G Q odd f onto ab X Y hX hY hne newGen
        change f Y = (f X)^(4:ℤ) at c
        simpa only [zpow_ofNat] using c
      · apply p025 G Q odd f onto ab X Y hX hY hne newGen
        change (f X)^(5:ℤ) = (f Y)^(2:ℤ) at c
        simpa only [zpow_ofNat] using c
      · apply first G Q odd f onto ab X Y hX hY hne newGen
        change (f X)^(3:ℤ) = 1 at c
        simpa only [zpow_ofNat] using c
      · apply second G Q odd f onto ab X Y hX hY hne newGen
        rw [sub_eq_add_neg] at c
        change (f Y * ((f X)^(2:ℤ))⁻¹)^(3:ℤ) = 1 at c
        simpa only [zpow_ofNat] using c
    obtain ⟨n,hn,hc⟩ := newGood
    exact ⟨n,hn,tr n hc⟩

theorem normalized_with {G : Type u} [Group G] [Finite G]
    (p013 : Solver.{u} (fun _ _ X Y => Y = X^3))
    (p014 : Solver.{u} (fun _ _ X Y => Y = X^4))
    (p025 : Solver.{u} (fun _ _ X Y => X^5 = Y^2))
    (first : Solver.{u} (fun _ _ X _ => X^3 = 1))
    (second : Solver.{u} (fun _ _ X Y => (Y * (X^2)⁻¹)^3 = 1))
    (odd : Odd (Nat.card G)) (met : Meta G) (x y : G)
    (hx : x ≠ 1) (hy : y ≠ 1) (ne : x ≠ y) : Good x y := by
  apply extend_from_generated x y odd met hx hy ne
  intro S _ _ X Y oddS metS gen hX hY hXY
  exact extension_with p013 p014 p025 first second oddS Abelianization.of ab_map_surj
    (ab_map_normal metS) X Y hX hY hXY gen

theorem arbitrary_with {G : Type u} [Group G] [Finite G]
    (p013 : Solver.{u} (fun _ _ X Y => Y = X^3))
    (p014 : Solver.{u} (fun _ _ X Y => Y = X^4))
    (p025 : Solver.{u} (fun _ _ X Y => X^5 = Y^2))
    (first : Solver.{u} (fun _ _ X _ => X^3 = 1))
    (second : Solver.{u} (fun _ _ X Y => (Y * (X^2)⁻¹)^3 = 1))
    (odd : Odd (Nat.card G)) (met : Meta G) (r s t : G)
    (hr : r ≠ s) (ht : r ≠ t) (hs : s ≠ t) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAnyPorts.HasPortCycle r s t n := by
  obtain ⟨hx,hy,ne⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨n,hn,hc⟩ := normalized_with p013 p014 p025 first second odd met _ _ hx hy ne
  exact ⟨n,hn,HaarAnyPorts.map_cycle r s t hc⟩

end HaarMetaFullOdd

#print axioms HaarMetaFullOdd.arbitrary_with
