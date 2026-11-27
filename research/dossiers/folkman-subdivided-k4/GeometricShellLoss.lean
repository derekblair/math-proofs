import GeometricActualShellBound

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A triangle is lost at its first vertex only if one of its two
incident edges has excessive spherical height. This costs at most
twice the one-coordinate bound. -/
theorem triangle_shell_lost_mass (m : ℕ) (dim : Module.finrank ℝ E=3+m+1)
    (t A : ℝ) (t0 : 0<t) (t1 : t≤1/8)
    (large : 36≤(m:ℝ)/2) (dense : 1≤((m:ℝ)/2)*t^2) :
    let w := A/(((m:ℝ)/2)*t)
    excessTriangleMass (E:=E) t
      (triangleExcessRegion t ∩ {p | w≤p.1 ∨ w≤p.2.1}) ≤
        (2*ENNReal.ofReal (Real.exp (36-A))) *
          excessTriangleMass (E:=E) t (triangleExcessRegion t) := by
  intro w
  let G := triangleExcessRegion t
  let L := G ∩ (Ici w ×ˢ (Ici 0 ×ˢ Ici 0))
  let R := G ∩ (Ici 0 ×ˢ (Ici w ×ˢ Ici 0))
  let k := ((m:ℝ)/2)*t
  have kp : 0<k := mul_pos (by linarith only [large]) t0
  have eq : k*w=A := by change k*(A/k)=A; field_simp [ne_of_gt kp]
  have lift : G ∩ {p | w≤p.1 ∨ w≤p.2.1} ⊆ L ∪ R := by
    intro p hp
    have q := triangleExcessRegion_within t hp.1
    rcases hp.2 with l|r
    · exact Or.inl ⟨hp.1,l,q.2.1.1,q.2.2.1⟩
    · exact Or.inr ⟨hp.1,q.1.1,r,q.2.2.1⟩
  have l := sphere_triangle_excess_tail (E:=E) m dim t w 0 0 t0 t1 large dense
  have r := sphere_triangle_excess_tail (E:=E) m dim t 0 w 0 t0 t1 large dense
  change excessTriangleMass (E:=E) t L ≤ ENNReal.ofReal (Real.exp (36-k*(w+0+0))) *
    excessTriangleMass (E:=E) t G at l
  change excessTriangleMass (E:=E) t R ≤ ENNReal.ofReal (Real.exp (36-k*(0+w+0))) *
    excessTriangleMass (E:=E) t G at r
  simp only [zero_add,add_zero,eq] at l r
  have union : excessTriangleMass (E:=E) t (L∪R) ≤
      excessTriangleMass (E:=E) t L + excessTriangleMass (E:=E) t R := by
    unfold excessTriangleMass
    rw [Set.preimage_union]
    exact measure_union_le _ _
  calc
    _ ≤ excessTriangleMass (E:=E) t (L∪R) := measure_mono (Set.preimage_mono lift)
    _ ≤ _ := union
    _ ≤ _ := add_le_add l r
    _ = _ := by rw [←add_mul,←two_mul]

#print axioms triangle_shell_lost_mass
end RobustFolkman.GeometricGap
