import C064Checked

namespace C064.Tenth

def W : Nat := 749513009868723669066958919875511371508404090751

theorem no_positive_below (i : Nat) (pos : 0<i) (lt : i<W) :
    31655*i ≠ clMul 32747 i := by
  intro E
  obtain ⟨o,_,oi,odd,h⟩ := odd_solution_of_solution i pos E
  have D : o=2*(o/2)+1 := by omega
  have S : 0+31655*(2*(o/2)+1)=0 ^^^ clMul 32747 (2*(o/2)+1) := by
    rw [←D]
    simpa using h
  have S' : 15827+31655*(o/2)=16373 ^^^ clMul 32747 (o/2) := by
    simpa using carryEq_step_odd S
  have rootC : (table 0).c=15827 := by decide +kernel
  have rootR : (table 0).r=16373 := by decide +kernel
  have rootB : (table 0).budget=W/2 := by decide +kernel
  have wp : W%2=1 := by decide +kernel
  have half : o/2<(table 0).budget := by rw [rootB]; omega
  exact no_residual table size all_checked (o/2) 0 (by decide) half
    (by simpa only [rootC,rootR] using S')

theorem witness_product : clMul 32747 W = 23725834327394447744314584608659312465098531492722905 := by
  decide +kernel

theorem witness_ordinary : 31655*W = 23725834327394447744314584608659312465098531492722905 := by
  decide +kernel

theorem exact_least : IsLeast {i : Nat | 0<i ∧ 31655*i = clMul 32747 i} W := by
  refine ⟨⟨by decide,witness_ordinary.trans witness_product.symm⟩,?_⟩
  intro i hi
  have H : 0<i ∧ 31655*i = clMul 32747 i := hi
  by_contra K
  exact no_positive_below i H.1 (by omega) H.2

theorem no_positive_at_tenth (i : Nat) (pos : 0<i) (le : i≤32747^10) :
    31655*i ≠ clMul 32747 i :=
  no_positive_below i pos (le.trans_lt (by decide +kernel))

#print axioms exact_least
#print axioms no_positive_at_tenth
end C064.Tenth
