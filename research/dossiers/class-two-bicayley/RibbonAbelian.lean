import Ribbon

namespace Ribbon
variable {G : Type*} [Group G]

/-- A common rim edge, joined by the two spokes, is a 4-cycle. -/
theorem shared_edge4 (a b : G) (ha : a≠1) (h : a=b ∨ a*b=1) : Cycle a b 4 := by
  let f : Fin 4 → Bool × G := ![(false,1),(false,a),(true,a),(true,1)]
  refine ⟨f,?_,?_⟩
  · intro i j eq
    fin_cases i <;> fin_cases j <;> (norm_num [f] at eq) <;> first | rfl | contradiction | exact False.elim (ha eq.symm)
  · intro i
    fin_cases i <;> norm_num [Adj,f]
    rcases h with h|h
    · exact Or.inr h.symm
    · exact Or.inl h

/-- Ordinary commuting rectangle, with all four corners in both rims. -/
theorem commute_eight (a b : G) (hab : Commute a b) (ha : a≠1) (hb : b≠1)
    (hne : a≠b) (hninv : a*b≠1) : Cycle a b 8 := by
  let corner : Fin 4 → G := ![1,a,a*b,b]
  have ci : Function.Injective corner := by
    have hs : a*b≠a := by intro E; apply hb; exact mul_left_cancel (E.trans (mul_one a).symm)
    have ht : a*b≠b := by intro E; apply ha; exact mul_right_cancel (E.trans (one_mul b).symm)
    intro i j E
    fin_cases i <;> fin_cases j <;> (norm_num [corner] at E) <;>
      first | rfl | contradiction | exact False.elim (ha E.symm) |
        exact False.elim (hb E.symm) | exact False.elim (hs E.symm) |
        exact False.elim (ht E.symm) | exact False.elim (hne E.symm) |
        exact False.elim (hninv E.symm)
  let rim : Fin 8 → Bool := ![false,false,true,true,false,false,true,true]
  let pos : Fin 8 → Fin 4 := ![0,1,1,2,2,3,3,0]
  let f : Fin 8 → Bool × G := fun i => (rim i,corner (pos i))
  refine ⟨f,?_,?_⟩
  · have H : ∀ i j : Fin 8, rim i=rim j → pos i=pos j → i=j := by decide +kernel
    intro i j e
    exact H i j (congrArg Prod.fst e) (ci (congrArg Prod.snd e))
  · intro i
    fin_cases i <;> norm_num [Adj,f,rim,pos,corner]
    exact Or.inr hab.eq.symm

theorem commute_dyadic (a b : G) (hab : Commute a b) (ha : a≠1) (hb : b≠1) :
    Cycle a b 4 ∨ Cycle a b 8 := by
  by_cases he : a=b
  · exact Or.inl (shared_edge4 a b ha (Or.inl he))
  by_cases hi : a*b=1
  · exact Or.inl (shared_edge4 a b ha (Or.inr hi))
  exact Or.inr (commute_eight a b hab ha hb he hi)

theorem class2_pair (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (rel : a*b=b*a*c) (ha : a≠1) (hb : b*b≠1) :
    Cycle a b 4 ∨ Cycle a b 8 ∨ Cycle a b 16 := by
  by_cases hc : c=1
  · have hb' : b≠1 := fun h => hb (by simp [h])
    have h : Commute a b := by change a*b=b*a; simpa [hc] using rel
    exact (commute_dyadic a b h ha hb').imp_right Or.inl
  · rcases noncommuting a b c ca cb rel hc hb with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end Ribbon
#print axioms Ribbon.class2_pair
