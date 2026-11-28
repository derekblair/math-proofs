import RamseyExooRows0
import RamseyExooRows1
import RamseyExooRows2
import RamseyExooRows3
import RamseyExooRows4
import RamseyExooRows5
import RamseyExooRows6
import RamseyExooRows7
import RamseyExooRows8
import RamseyExooRows9

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem rows (a : Fin 46) : rowCheck a = false := by
  exact Fin.cases bound_0 (Fin.cases bound_1 (Fin.cases bound_2 (Fin.cases bound_3 (Fin.cases bound_4 (Fin.cases bound_5 (Fin.cases bound_6 (Fin.cases bound_7 (Fin.cases bound_8 (Fin.cases bound_9 (Fin.cases bound_10 (Fin.cases bound_11 (Fin.cases bound_12 (Fin.cases bound_13 (Fin.cases bound_14 (Fin.cases bound_15 (Fin.cases bound_16 (Fin.cases bound_17 (Fin.cases bound_18 (Fin.cases bound_19 (Fin.cases bound_20 (Fin.cases bound_21 (Fin.cases bound_22 (Fin.cases bound_23 (Fin.cases bound_24 (Fin.cases bound_25 (Fin.cases bound_26 (Fin.cases bound_27 (Fin.cases bound_28 (Fin.cases bound_29 (Fin.cases bound_30 (Fin.cases bound_31 (Fin.cases bound_32 (Fin.cases bound_33 (Fin.cases bound_34 (Fin.cases bound_35 (Fin.cases bound_36 (Fin.cases bound_37 (Fin.cases bound_38 (Fin.cases bound_39 (Fin.cases bound_40 (Fin.cases bound_41 (Fin.cases bound_42 (Fin.cases bound_43 (Fin.cases bound_44 (Fin.cases bound_45 (fun t : Fin 0 => t.elim0)) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) a

theorem triangles (a : Fin 46) : tfCheck a = true := by
  exact Fin.cases tri_0 (Fin.cases tri_1 (Fin.cases tri_2 (Fin.cases tri_3 (Fin.cases tri_4 (Fin.cases tri_5 (Fin.cases tri_6 (Fin.cases tri_7 (Fin.cases tri_8 (Fin.cases tri_9 (Fin.cases tri_10 (Fin.cases tri_11 (Fin.cases tri_12 (Fin.cases tri_13 (Fin.cases tri_14 (Fin.cases tri_15 (Fin.cases tri_16 (Fin.cases tri_17 (Fin.cases tri_18 (Fin.cases tri_19 (Fin.cases tri_20 (Fin.cases tri_21 (Fin.cases tri_22 (Fin.cases tri_23 (Fin.cases tri_24 (Fin.cases tri_25 (Fin.cases tri_26 (Fin.cases tri_27 (Fin.cases tri_28 (Fin.cases tri_29 (Fin.cases tri_30 (Fin.cases tri_31 (Fin.cases tri_32 (Fin.cases tri_33 (Fin.cases tri_34 (Fin.cases tri_35 (Fin.cases tri_36 (Fin.cases tri_37 (Fin.cases tri_38 (Fin.cases tri_39 (Fin.cases tri_40 (Fin.cases tri_41 (Fin.cases tri_42 (Fin.cases tri_43 (Fin.cases tri_44 (Fin.cases tri_45 (fun t : Fin 0 => t.elim0)) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) a

theorem graph_symmetric : ∀ a b, graph a b → graph b a := by
  decide +kernel

theorem graph_irreflexive : ∀ a, ¬ graph a a := by
  decide +kernel

theorem triangle_free : TriangleFree graph := tfCheck_sound triangles

theorem alpha_le_ten (S : Finset (Fin 46)) (h : Independent graph S) : S.card ≤ 10 :=
  bound_of_per_vertex adj 10 rows S h

theorem ramsey311_ge47 :
    ∃ R : Fin 46 → Fin 46 → Prop, (∀ a b, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧
      TriangleFree R ∧ (∀ S : Finset (Fin 46), Independent R S → S.card ≤ 10) :=
  ⟨graph, graph_symmetric, graph_irreflexive, triangle_free, alpha_le_ten⟩

#print axioms ramsey311_ge47
end Erdos151Ramsey.Exoo
