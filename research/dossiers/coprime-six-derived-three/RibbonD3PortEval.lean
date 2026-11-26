import RibbonD3SchreierSound
import Ribbon5Family

namespace RibbonD3PortEval
open RibbonD3MateData Ribbon5Bridge RibbonD3Grid RibbonD3SignedEval
variable {G : Type*} [Group G]

def enc (w : List P) := w.map Fin.val

def decode (w : List Nat) : List P :=
  w.map (fun z => ⟨z % 3, by omega⟩)

theorem enc_decode (w : List Nat) (h : ∀ z ∈ w, z < 3) :
    enc (decode w) = w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    have hz := h z (by simp)
    have hw : ∀ j ∈ w, j < 3 := fun j hj => h j (List.mem_cons_of_mem _ hj)
    change (z%3) :: enc (decode w) = _
    rw [ih hw,Nat.mod_eq_of_lt hz]

theorem eval_encode (x y : G) (b : Bool) (w : List P) :
    eval (letter x y) (erasePorts b (enc w)) = Ribbon5Law.trace x y b w := by
  induction w generalizing b with
  | nil => rfl
  | cons d w ih =>
    change _ = _ 
    have e : enc (d::w) = d.val :: enc w := rfl
    rw [e]
    cases b <;> fin_cases d <;>
      simp [erasePorts,eval,letter,Ribbon5Law.trace,ih]

theorem eval_port_snd (x y : G) (b : Bool) (w : List Nat) (h : ∀ z ∈ w, z < 3) :
    eval (letter x y) (erasePorts b w) = (run x y (b,1) (decode w)).2 := by
  rw [run_trace,one_mul,←eval_encode,enc_decode w h]

theorem legal_erase (b : Bool) (w : List Nat) :
    ∀ a ∈ erasePorts b w, legal a := by
  induction w generalizing b with
  | nil => simp [erasePorts]
  | cons d w ih =>
    by_cases h2 : d = 2
    · subst d
      simpa [erasePorts] using ih (!b)
    · cases b <;> by_cases h0 : d=0 <;>
       simp only [erasePorts,h2,h0,beq_iff_eq,if_true,if_false,Bool.false_eq_true] <;>
       intro a ha <;> rcases List.mem_cons.mp ha with e|e <;>
       first | (subst a; unfold legal; decide) | (exact ih _ a e)

theorem legal_inverse (w : List Int) (h : ∀ a ∈ w, legal a) :
    ∀ a ∈ inverse w, legal a := by
  intro a ha
  obtain ⟨t,ht,E⟩ := List.mem_map.mp ha
  have ht' : t ∈ w := List.mem_reverse.mp ht
  rcases h t ht' with K|K|K|K <;> subst t <;> subst a <;> unfold legal <;> decide

theorem legal_power {z : Int} (hz : legal z) (n : Int) :
    ∀ a ∈ repeatPower z n, legal a := by
  intro a ha
  have e := List.eq_of_mem_replicate ha
  subst a
  by_cases ht : n < 0
  · rcases hz with K|K|K|K <;> subst z <;> simp [legal,ht]
  · simpa [ht] using hz

#print axioms eval_port_snd
end RibbonD3PortEval
