import GeometricNormalizedCut

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {V : Type*} [DecidableEq V] [Fintype V]

def orderedEdge (q : V×V) : Finset V := {q.1,q.2}
def directedEdges (L : EdgeGraph V) : Finset (V×V) :=
  (Finset.univ : Finset (V×V)).filter (fun q => q.1≠q.2 ∧ orderedEdge q∈L)

noncomputable def linkAdjMatrix (L : EdgeGraph V) : Matrix V V ℝ :=
  fun i j => if i≠j ∧ ({i,j}:Finset V)∈L then 1 else 0

theorem linkAdjMatrix_symm (L : EdgeGraph V) : (linkAdjMatrix L).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply,linkAdjMatrix]
  rw [Finset.pair_comm j i]
  split <;> split <;> simp_all [Ne.symm]

theorem linkAdjMatrix_nonneg (L : EdgeGraph V) (i j : V) : 0≤linkAdjMatrix L i j := by
  unfold linkAdjMatrix
  split <;> norm_num

theorem pair_orientation {a b i j : V} (ij : i≠j)
    (h : ({i,j}:Finset V)={a,b}) :
    (i=a ∧ j=b) ∨ (i=b ∧ j=a) := by
  have x : i∈({a,b}:Finset V) := h ▸ (by simp : i∈({i,j}:Finset V))
  have y : j∈({a,b}:Finset V) := h ▸ (by simp : j∈({i,j}:Finset V))
  simp only [mem_insert,mem_singleton] at x y
  rcases x with rfl|rfl <;> rcases y with rfl|rfl <;> first | contradiction | simp

theorem directed_fiber_pair (L : EdgeGraph V) (a b : V) (ab : a≠b)
    (h : ({a,b}:Finset V)∈L) :
    (directedEdges L).filter (fun q => orderedEdge q=({a,b}:Finset V)) =
      {(a,b),(b,a)} := by
  ext q
  rcases q with ⟨i,j⟩
  simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  have hh : (i,j)∈directedEdges L ↔ i≠j ∧ ({i,j}:Finset V)∈L := by
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  rw [hh]
  change ((i≠j ∧ ({i,j}:Finset V)∈L) ∧ ({i,j}:Finset V)={a,b}) ↔ _
  constructor
  · intro p
    exact pair_orientation p.1.1 p.2
  · rintro (⟨ha,hb⟩|⟨ha,hb⟩)
    · subst i
      subst j
      exact ⟨⟨ab,h⟩,rfl⟩
    · subst i
      subst j
      rw [Finset.pair_comm b a]
      exact ⟨⟨ab.symm,h⟩,rfl⟩

theorem directed_sum_by_edge (L : EdgeGraph V) (f : V→V→ℝ) :
    (∑ i, ∑ j, linkAdjMatrix L i j*f i j) =
      ∑ e∈L, ∑ q∈(directedEdges L).filter (fun q => orderedEdge q=e), f q.1 q.2 := by
  have Z : (∑ i, ∑ j, linkAdjMatrix L i j*f i j) =
      ∑ q∈directedEdges L, f q.1 q.2 := by
    unfold directedEdges
    rw [Finset.sum_filter,← Finset.univ_product_univ,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i≠j ∧ ({i,j}:Finset V)∈L <;> simp [linkAdjMatrix,orderedEdge,h]
  rw [Z]
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro q h
  exact (mem_filter.mp h).2.2

theorem directed_orient_count (L : EdgeGraph V) (two : ∀ e∈L, (e : Finset V).card=2) :
    (∑ i, ∑ j, linkAdjMatrix L i j)=2*(L.card:ℝ) := by
  have h := directed_sum_by_edge L (fun _ _ => (1:ℝ))
  simp only [mul_one] at h
  rw [h]
  have q (e : Finset V) (he : e∈L) :
      (∑ q∈(directedEdges L).filter (fun q => orderedEdge q=e), (1:ℝ))=2 := by
    obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp (two e he)
    rw [directed_fiber_pair L a b ab he]
    have ne : (a,b)≠(b,a) := fun ex => ab (congrArg Prod.fst ex)
    rw [Finset.sum_pair ne]
    norm_num
  rw [Finset.sum_congr rfl q]
  simp [mul_comm]

open scoped Classical in
theorem directed_cut_count (L : EdgeGraph V) (two : ∀ e∈L, (e : Finset V).card=2)
    (b : V→Bool) :
    (∑ i, ∑ j, linkAdjMatrix L i j*edgeFlip b i j)=
      2*(∑ e∈L, if Monochrom b e then (0:ℝ) else 1) := by
  rw [directed_sum_by_edge]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨x,y,xy,rfl⟩ := Finset.card_eq_two.mp (two e he)
  rw [directed_fiber_pair L x y xy he]
  have ne : (x,y)≠(y,x) := fun ex => xy (congrArg Prod.fst ex)
  rw [Finset.sum_pair ne]
  simp only [mono_two_iff,edgeFlip]
  by_cases eq : b x=b y <;> norm_num [eq,eq_comm]

#print axioms directed_orient_count
#print axioms directed_cut_count
end RobustFolkman.GeometricGap
