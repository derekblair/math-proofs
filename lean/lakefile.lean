import Lake
open Lake DSL

package mathproofs where
  version := v!"0.1.0"
  fixedToolchain := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib Mathproofs where

lean_lib Mathproofs.NumberTheory where

lean_lib Mathproofs.Combinatorics where

lean_lib Mathproofs.Topology where

lean_lib Mathproofs.Dynamics where

lean_lib ComparatorChallenges where
  globs := #[.submodules `ComparatorChallenges]

-- Post-scope Seam B / Seam C libraries preserved without invented remapping (see DISCREPANCY.md)
lean_lib MathProofs where
  globs := #[.submodules `MathProofs]

lean_lib SeamC where
  globs := #[.submodules `SeamC]

@[default_target]
lean_exe mathproofs where
  root := `Main
