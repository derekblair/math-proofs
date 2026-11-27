import C064Checked

namespace C064.Ninth

def W : Nat := 10818005328236238993612085342811863575

theorem no_positive_below (i : Nat) (pos : 0<i) (lt : i<W) :
    7935*i ≠ clMul 8179 i := by
  intro E
  obtain ⟨o,_,oi,odd,h⟩ := odd_solution_of_solution i pos E
  have D : o=2*(o/2)+1 := by omega
  have S : 0+7935*(2*(o/2)+1)=0 ^^^ clMul 8179 (2*(o/2)+1) := by
    rw [←D]
    simpa using h
  have S' : 3967+7935*(o/2)=4089 ^^^ clMul 8179 (o/2) := by
    simpa using carryEq_step_odd S
  have rootC : (table 0).c=3967 := by decide +kernel
  have rootR : (table 0).r=4089 := by decide +kernel
  have rootB : (table 0).budget=W/2 := by decide +kernel
  have wp : W%2=1 := by decide +kernel
  have half : o/2<(table 0).budget := by rw [rootB]; omega
  exact no_residual table size all_checked (o/2) 0 (by decide) half
    (by simpa only [rootC,rootR] using S')

theorem witness_product : clMul 8179 W = 85840872279554556414311897195212137467625 := by
  decide +kernel

theorem witness_ordinary : 7935*W = 85840872279554556414311897195212137467625 := by
  decide +kernel

theorem exact_least : IsLeast {i : Nat | 0<i ∧ 7935*i = clMul 8179 i} W := by
  refine ⟨⟨by decide,witness_ordinary.trans witness_product.symm⟩,?_⟩
  intro i hi
  have H : 0<i ∧ 7935*i = clMul 8179 i := hi
  by_contra K
  exact no_positive_below i H.1 (by omega) H.2

theorem no_positive_at_ninth (i : Nat) (pos : 0<i) (le : i≤8179^9) :
    7935*i ≠ clMul 8179 i :=
  no_positive_below i pos (le.trans_lt (by decide +kernel))

#print axioms exact_least
#print axioms no_positive_at_ninth
end C064.Ninth
