import TableDiagonal
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter Set Topology Function
open scoped BigOperators
namespace SparseHalfGraphon

/-- Numerical masses and rectangle integrals on nested finite partitions.
Only identities preserved by coordinatewise convergence are required. -/
structure CoherentTables (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] (p : ∀ n, I (n+1) → I n) where
  cell : ∀ n, I n → ℝ
  joint : ∀ n, I n → I n → ℝ
  cell_zero : ∀ n i, 0 ≤ cell n i
  cell_total : ∀ n, ∑ i, cell n i = 1
  cell_split : ∀ n i, cell n i = ∑ a with p n a = i, cell (n+1) a
  joint_zero : ∀ n i j, 0 ≤ joint n i j
  joint_bound : ∀ n i j, joint n i j ≤ cell n i * cell n j
  joint_symm : ∀ n i j, joint n i j = joint n j i
  joint_split : ∀ n i j, joint n i j =
    ∑ a with p n a = i, ∑ b with p n b = j, joint (n+1) a b

/-- Limit tables conserve mass and preserve nested consistency. Only
eventual stabilization at each level, not global stabilization, is needed. -/
noncomputable def limit_coherent_tables {I : ℕ→Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    {p : ∀ n, I (n+1) → I n} {P : ℕ → ∀ n, I (n+1) → I n}
    (A : ∀ k : ℕ, CoherentTables I (P k))
    (hp : ∀ n, ∀ᶠ k in atTop, P k n = p n)
    (C : ∀ n, I n → ℝ) (J : ∀ n, I n → I n → ℝ)
    (hC : ∀ n i, Tendsto (fun k => (A k).cell n i) atTop (𝓝 (C n i)))
    (hJ : ∀ n i j, Tendsto (fun k => (A k).joint n i j) atTop (𝓝 (J n i j))) :
    CoherentTables I p where
  cell := C
  joint := J
  cell_zero := fun n i => le_of_tendsto_of_tendsto' tendsto_const_nhds (hC n i)
    (fun k => (A k).cell_zero n i)
  cell_total := by
    intro n
    have hs := tendsto_finsetSum Finset.univ (fun i _ => hC n i)
    exact tendsto_nhds_unique hs (by simpa only [funext (fun k => (A k).cell_total n)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
  cell_split := by
    intro n i
    have hs := tendsto_finsetSum (Finset.univ.filter (fun a => p n a = i))
      (fun a _ => hC (n+1) a)
    have eq : (fun k => ∑ a with p n a = i, (A k).cell (n+1) a) =ᶠ[atTop]
        (fun k => (A k).cell n i) := by
      filter_upwards [hp n] with k hk
      simpa only [hk] using ((A k).cell_split n i).symm
    exact tendsto_nhds_unique (hC n i) (hs.congr' eq)
  joint_zero := fun n i j => le_of_tendsto_of_tendsto' tendsto_const_nhds (hJ n i j)
    (fun k => (A k).joint_zero n i j)
  joint_bound := fun n i j => le_of_tendsto_of_tendsto' (hJ n i j) ((hC n i).mul (hC n j))
    (fun k => (A k).joint_bound n i j)
  joint_symm := by
    intro n i j
    have eq : (fun k => (A k).joint n i j) = (fun k => (A k).joint n j i) :=
      funext fun k => (A k).joint_symm n i j
    exact tendsto_nhds_unique (hJ n i j) (eq ▸ hJ n j i)
  joint_split := by
    intro n i j
    have hs := tendsto_finsetSum (Finset.univ.filter (fun a => p n a = i))
      (fun a _ => tendsto_finsetSum (Finset.univ.filter (fun b => p n b = j))
        (fun b _ => hJ (n+1) a b))
    have eq : (fun k => ∑ a with p n a = i, ∑ b with p n b = j, (A k).joint (n+1) a b) =ᶠ[atTop]
        (fun k => (A k).joint n i j) := by
      filter_upwards [hp n] with k hk
      simpa only [hk] using ((A k).joint_split n i j).symm
    exact tendsto_nhds_unique (hJ n i j) (hs.congr' eq)

#print axioms limit_coherent_tables
end SparseHalfGraphon
