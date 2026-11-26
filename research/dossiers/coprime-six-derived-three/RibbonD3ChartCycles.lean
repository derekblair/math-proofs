import RibbonD3VertexMates
import RibbonD3CoverUse

namespace RibbonD3ChartCycles
open RibbonD3MateData RibbonD3MateUse RibbonD3PortEval RibbonD3SignedEval
open RibbonD3WordSelection RibbonD3VertexMates Ribbon5Bridge RibbonDerived3
open RibbonD3Field (label raw)
variable {G : Type*} [Group G]

theorem length_block (k : Count) (n : Nat) (h : n ≤ 128) :
    (block k n).length = n := by
  have h0 := (data_valid k).2.1
  simp only [block,decode,List.length_map,List.length_take] at h0 ⊢
  exact Nat.min_eq_left (h.trans (h0 ▸ Nat.min_le_right _ _))

theorem path_prefix (x y : G) (k : Count) (n a : Nat) (ha : a ≤ n) :
    pathAt x y (block k n).toArray a = vertex x y k a := by
  simp [pathAt,vertex,block,decode,List.map_take,List.take_take,Nat.min_eq_left ha]

/-- The combinatorial/word layer needs only collision-to-label soundness:
one field, two fields, a jet, or a small nilpotent quotient may supply it. -/
theorem from_chart (d3 : DLS G 3 = ⊥) (x y : G) (k : Count)
    (coll : ∀ a b : Fin 128, vertex x y k a.val = vertex x y k b.val →
      label (raw (RibbonD3Field.chart k) a.val) = label (raw (RibbonD3Field.chart k) b.val)) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  have zero : vertex x y k 0 = start G := rfl
  by_cases R : rat x y k = 1
  · left
    apply cycle_from_at x y (block k 32).toArray (by simpa using length_block k 32 (by decide))
    · rw [path_prefix x y k 32 32 le_rfl,path_prefix x y k 32 0 (Nat.zero_le _)]
      rw [zero]
      change run x y (start G) (block k 32) = start G
      rw [runA,R]
      simp [shift]
    · intro a b ab eq
      rw [path_prefix x y k 32 a.val a.isLt.le,path_prefix x y k 32 b.val b.isLt.le] at eq
      let i : Fin 128 := ⟨a.val,by have := a.isLt; omega⟩
      let j : Fin 128 := ⟨b.val,by have := b.isLt; omega⟩
      rcases selected_cover k (a:=i) (b:=j) ab (coll i j eq) with H|⟨u,_,hj⟩
      · exact (Nat.not_le_of_gt (b.isLt.trans (by decide : 32 < 64))) H.1
      · have e := (exact_information (idx k) u)
        have q : ((exactRows[k.val]!)[u]).baseLength ≤ b.val := by
          have t := e.2.2.1
          change ((exactRows[k.val]!)[u]).baseLength ≤ ((exactRows[k.val]!)[u]).j at t
          rwa [hj] at t
        have bounds := e.1
        change ((exactRows[k.val]!)[u]).baseLength = 32 ∨
          ((exactRows[k.val]!)[u]).baseLength = 64 at bounds
        rcases bounds with h|h <;> omega
  · by_cases Z : zed x y k = 1
    · right; left
      apply cycle_from_at x y (block k 64).toArray (by simpa using length_block k 64 (by decide))
      · rw [path_prefix x y k 64 64 le_rfl,path_prefix x y k 64 0 (Nat.zero_le _)]
        rw [zero]
        change run x y (start G) (block k 64) = start G
        rw [runW,Z]
        simp [shift]
      · intro a b ab eq
        rw [path_prefix x y k 64 a.val a.isLt.le,path_prefix x y k 64 b.val b.isLt.le] at eq
        let i : Fin 128 := ⟨a.val,by have := a.isLt; omega⟩
        let j : Fin 128 := ⟨b.val,by have := b.isLt; omega⟩
        rcases selected_cover k (a:=i) (b:=j) ab (coll i j eq) with H|⟨u,hi,hj⟩
        · exact (Nat.not_le_of_gt b.isLt) H.1
        · have e := (exact_information (idx k) u)
          have bounds := e.1
          change ((exactRows[k.val]!)[u]).baseLength = 32 ∨
            ((exactRows[k.val]!)[u]).baseLength = 64 at bounds
          have h : ((exactRows[k.val]!)[u]).baseLength = 32 := by
            rcases bounds with H|H
            · exact H
            · have t := e.2.2.1
              change ((exactRows[k.val]!)[u]).baseLength ≤ ((exactRows[k.val]!)[u]).j at t
              rw [H,hj] at t
              exact False.elim ((Nat.not_le_of_gt b.isLt) t)
          apply R
          have e' := exact_collision_residue x y k u (by
            change vertex x y k ((exactRows[k.val]!)[u]).i =
              vertex x y k ((exactRows[k.val]!)[u]).j
            rw [hi,hj]; exact eq)
          change (if ((exactRows[k.val]!)[u]).baseLength = 32
            then rat x y k = 1 else zed x y k = 1) at e'
          rwa [if_pos h] at e'
    · right; right
      apply cycle_from_at x y (block k 128).toArray (by simpa using length_block k 128 (by decide))
      · rw [path_prefix x y k 128 128 le_rfl,path_prefix x y k 128 0 (Nat.zero_le _)]
        rw [zero]
        exact runClosed d3 x y k
      · intro a b ab eq
        rw [path_prefix x y k 128 a.val a.isLt.le,path_prefix x y k 128 b.val b.isLt.le] at eq
        rcases selected_cover k ab (coll a b eq) with ⟨_,u,hi,hj⟩|⟨u,hi,hj⟩
        · have M : charts[k.val]! = mc k := getElem!_pos charts k.val (idx k).isLt
          have hu : u.val < (mc k).rows.size := by simpa [←M] using u.isLt
          let v : Fin (mc k).rows.size := ⟨u.val,hu⟩
          have same : (mc k).rows[v] = charts[k.val]!.rows[u] := by
            change (mc k).rows[u.val] = charts[k.val]!.rows[u.val]
            rw [←getElem!_pos (mc k).rows u.val hu,
              ←getElem!_pos charts[k.val]!.rows u.val u.isLt]
            exact congrArg (fun c : Chart => c.rows[u.val]!) M.symm
          have q := mod_collision_residue x y k v (by
            rw [same,hi,hj]
            exact eq)
          exact RibbonD3Closure.base_nontrivial_mod_third d3 (RibbonD3ClosureMembership.U_mem_derived x y (idx k)) Z q
        · have e' := exact_collision_residue x y k u (by
            change vertex x y k ((exactRows[k.val]!)[u]).i =
              vertex x y k ((exactRows[k.val]!)[u]).j
            rw [hi,hj]; exact eq)
          change (if ((exactRows[k.val]!)[u]).baseLength = 32
            then rat x y k = 1 else zed x y k = 1) at e'
          by_cases h : ((exactRows[k.val]!)[u]).baseLength = 32
          · rw [if_pos h] at e'
            exact R e'
          · rw [if_neg h] at e'
            exact Z e' 

#print axioms from_chart
end RibbonD3ChartCycles
