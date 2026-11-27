import HaarClass4Normal
import HaarVoltageLift

namespace HaarClass4Graph
open HaarCycle HaarAllNoncommuting HaarVoltage HaarVoltageLift HaarClass4Normal HaarClass4Table

variable {G : Type*} [Group G]

def valid (r : Row) := r.i= -2 ∨ r.i= -1 ∨ r.i=0 ∨ r.i=1
instance (r : Row) : Decidable (valid r) := by unfold valid; infer_instance

theorem rows_valid (i : Fin 33) : valid (ordinary i.val) ∧ valid (conditional i.val) := by
  revert i
  decide

def vert (M : Data G) (T : ℕ → Row) (i : Fin 32) := (side i, eval M (T i.val))

theorem norm_edge (M : Data G) {p q : Row} (hp : valid p) (e : reaches p q) :
    eval M q = eval M p ∨ eval M q = eval M p*M.x ∨ eval M q = eval M p*M.y := by
  rcases e with rfl|rfl|rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (eval_x M p))
  · exact Or.inr (Or.inr (eval_y M p hp))

theorem valid_succ (i : Fin 32) : i.val+1 < 33 := by omega

theorem adj (M : Data G) (T : ℕ → Row)
    (hValid : ∀ i : Fin 33, valid (T i.val))
    (hStep : ∀ i : Fin 32, stepCondition T i)
    (hEnd : eval M (T 32) = eval M (T 0)) :
    ∀ i : Fin 32, haarAdj M.x M.y (vert M T i) (vert M T (i+1)) := by
  intro i
  have e : eval M (T (i+1).val) = eval M (T (i.val+1)) := by
    have hi : index 32 (i.val+1)=i+1 := by
      rw [index_succ,val_index]
    rw [← hi]
    change eval M (T ((i.val+1)%32)) = _
    by_cases he : i.val+1 < 32
    · rw [Nat.mod_eq_of_lt he]
    · have he' : i.val+1=32 := by have h0:=i.isLt; omega
      simpa only [he',Nat.mod_self] using hEnd.symm
  have ha := hValid ⟨i.val, by have h0 := i.isLt; omega⟩
  have hb := hValid ⟨i.val+1,valid_succ i⟩
  have hs := hStep i
  have he := differentSide i
  cases h1 : side i <;> cases h2 : side (i+1) <;>
    simp only [h1,h2,stepCondition,ite_true] at he hs
  · contradiction
  · simpa [vert,haarAdj,h1,h2,e] using norm_edge M ha hs
  · simpa [vert,haarAdj,h1,h2,e] using norm_edge M hb hs
  · contradiction

theorem normal_base (M : Data G) : eval M base = 1 := by
  simp [eval,base,mid,tail]

theorem normal_rebound (M : Data G) (F : M.c^3=M.u*M.v) (U : M.u^3=M.a*M.b)
    (A : M.a^3=1) : eval M rebound=1 := by
  have hv : Commute M.u M.v := M.huv
  have hb := M.cb M.a
  calc
    eval M rebound = M.c^3 * M.u^2 * M.v⁻¹ * M.a^2 * M.b⁻¹ := by
      norm_num [eval,rebound,mid,tail,mul_assoc]
    _ = M.u^3 * M.a^2 * M.b⁻¹ := by
      rw [F,mul_assoc M.u M.v,(hv.symm.pow_right 2).eq]
      group
    _ = M.a^3 := by rw [U,mul_assoc M.a M.b,(hb.pow_right 2).eq]; group
    _ = 1 := A

theorem ordinary_adj (M : Data G) : ∀ i : Fin 32,
    haarAdj M.x M.y (vert M ordinary i) (vert M ordinary (i+1)) := by
  apply adj M ordinary (fun i => (rows_valid i).1) edges.1
  rw [ends.2.1,ends.1]

theorem conditional_adj (M : Data G) (F : M.c^3=M.u*M.v) (U : M.u^3=M.a*M.b)
    (A : M.a^3=1) :
    ∀ i : Fin 32, haarAdj M.x M.y (vert M conditional i) (vert M conditional (i+1)) := by
  apply adj M conditional (fun i => (rows_valid i).2) edges.2
  rw [ends.2.2.2,ends.2.2.1,normal_rebound M F U A,normal_base M]

end HaarClass4Graph

#print axioms HaarClass4Graph.ordinary_adj
#print axioms HaarClass4Graph.conditional_adj
