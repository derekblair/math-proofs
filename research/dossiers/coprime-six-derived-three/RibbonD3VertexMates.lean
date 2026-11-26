import RibbonD3WordSelection
import RibbonD3ExactUse

namespace RibbonD3VertexMates
open RibbonD3MateData RibbonD3MateUse RibbonD3PortEval RibbonD3SignedEval
open RibbonD3WordSelection Ribbon5Bridge RibbonDerived3
variable {G : Type*} [Group G]

def vertex (x y : G) (k : Count) (a : Nat) : Bool × G :=
  run x y (start G) (block k a)

theorem ratio_one (x y : G) (k : Count) {a b : Nat} (E : vertex x y k a = vertex x y k b) :
    eval (letter x y) (ratio (mc k) a b) = 1 := by
  unfold ratio
  rw [eval_append,eval_inverse _ (neg_letter x y),block_ok,block_ok]
  change (vertex x y k b).2 * (vertex x y k a).2⁻¹ = 1
  rw [E,mul_inv_cancel]

private theorem conj_extract (N : Subgroup G) [N.Normal] {u r : G}
    (h : u*r*u⁻¹ ∈ N) : r ∈ N := by
  have H := (inferInstance : N.Normal).conj_mem _ h u⁻¹
  simpa [←mul_assoc] using H

private theorem signed_conj_mem (N : Subgroup G) [N.Normal] (b : Bool) {u r : G}
    (h : u*(if b then r else r⁻¹)*u⁻¹ ∈ N) : r ∈ N := by
  have q := conj_extract N h
  cases b
  · simpa using N.inv_mem q
  · exact q

theorem exact_base_eval (x y : G) (k : Count) {n : Nat} (h : n = 32 ∨ n = 64) :
    eval (letter x y) (letters (mc k) n) =
    if n = 32 then rat x y k else zed x y k := by
  rcases h with rfl|rfl
  · simp [rat]
  · rw [if_neg (by decide : ¬64=32),block_ok,show (false,1) = start G from rfl,runW]
    simp [shift,start]

theorem exact_collision_residue (x y : G) (k : Count) (j : Fin (exactRows[k.val]!).size)
    (E : vertex x y k ((exactRows[k.val]!)[j]).i = vertex x y k ((exactRows[k.val]!)[j]).j) :
    if ((exactRows[k.val]!)[j]).baseLength = 32 then rat x y k = 1 else zed x y k = 1 := by
  let r := (exactRows[k.val]!)[j]
  have a := exact_mate_eval x y (idx k) j
  have h : charts[k.val]! = mc k := getElem!_pos charts k.val (idx k).isLt
  change eval (letter x y) (ratio charts[k.val]! r.i r.j) =
    eval (letter x y) (exactReference charts[k.val]! r) at a
  rw [h,ratio_one x y k E] at a
  unfold exactReference at a
  rw [eval_append,eval_append,eval_inverse _ (neg_letter x y)] at a
  have T : eval (letter x y) (if r.sign == 1 then letters (mc k) r.baseLength
      else inverse (letters (mc k) r.baseLength)) = 1 := by
    have q := congrArg (fun e => (eval (letter x y) r.conjugator)⁻¹ * e * eval (letter x y) r.conjugator) a.symm
    simpa [←mul_assoc] using q
  have er := exact_base_eval x y k (exact_information (idx k) j).1
  have e1 : eval (letter x y) (letters (mc k) r.baseLength) = 1 := by
    by_cases b : r.sign == 1
    · rwa [if_pos b] at T
    · rw [if_neg b,eval_inverse _ (neg_letter x y)] at T
      exact inv_eq_one.mp T
  change eval (letter x y) (letters (mc k) r.baseLength) =
    (if r.baseLength = 32 then rat x y k else zed x y k) at er
  change if r.baseLength = 32 then rat x y k = 1 else zed x y k = 1
  split_ifs with h
  · simpa [h] using er.symm.trans e1
  · simpa [h] using er.symm.trans e1

theorem mod_collision_residue (x y : G) (k : Count) (j : Fin (mc k).rows.size)
    (E : vertex x y k (mc k).rows[j].i = vertex x y k (mc k).rows[j].j) :
    rat x y k ∈ DLS G 2 := by
  let c := mc k
  let r := c.rows[j]
  have a := mateR_mod x y (idx k) j
  change eval (letter x y) (ratio c r.i r.j) *
    (eval (letter x y) (reference c r))⁻¹ ∈ DLS G 2 at a
  rw [ratio_one x y k E,one_mul] at a
  have p := (DLS G 2).inv_mem a
  rw [inv_inv] at p
  unfold reference at p
  rw [eval_append,eval_append,eval_inverse _ (neg_letter x y)] at p
  by_cases b : r.sign == 1
  · rw [if_pos b] at p
    exact conj_extract _ p
  · rw [if_neg b,eval_inverse _ (neg_letter x y)] at p
    have h := (DLS G 2).inv_mem (conj_extract _ p)
    rw [inv_inv] at h
    exact h

#print axioms exact_collision_residue
#print axioms mod_collision_residue
end RibbonD3VertexMates
