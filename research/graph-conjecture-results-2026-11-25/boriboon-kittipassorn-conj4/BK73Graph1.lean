import BK73Sound1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin

open SimpleGraph Finset

namespace BK73

/-- the 21 unordered pairs of `Fin 7`, in the order used by `pidx` -/
def EPf : List (Fin 7 × Fin 7) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),
   (2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

def codeList (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] : List Bool :=
  EPf.map (fun p => decide (G.Adj p.1 p.2))

theorem codeList_length (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] :
    (codeList G).length = 21 := by simp [codeList, EPf]

theorem ab_code (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] (i j : Fin 7) :
    ab (ofBits (codeList G)) i j = decide (G.Adj i j) := by
  unfold ab
  rw [testBit_ofBits]
  fin_cases i <;> fin_cases j <;> simp [codeList, EPf, pidx, G.adj_comm] <;> exact G.adj_comm _ _

theorem length_filter_range7 (f : ℕ → Bool) :
    ((List.range 7).filter f).length = ∑ j : Fin 7, (if f j then 1 else 0) := by
  rw [← List.countP_eq_length_filter, Fin.sum_univ_seven]
  simp [List.range_succ, List.countP_cons]
  omega

theorem degree_eq_sum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ w, (if G.Adj v w then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]

theorem deg_code (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] (i : Fin 7) :
    deg (ofBits (codeList G)) i = G.degree i := by
  rw [deg, length_filter_range7, degree_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ab_code]
  simp

theorem count_true_add_false (l : List Bool) : l.count true + l.count false = l.length := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [List.count_cons] <;> omega

theorem handshake_code (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] :
    ∑ i, G.degree i = 2 * (codeList G).count true := by
  simp only [degree_eq_sum, Fin.sum_univ_seven]
  simp [codeList, EPf, List.count_cons, G.adj_comm]
  omega

end BK73
