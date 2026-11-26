import HeawoodLift64Data
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace HeawoodLift64
open HaarOrbitC7Voltage (B P next)
open HomologyThree
open scoped BigOperators

def smallBump (u v : B) (i : Fin 8) : Z := bump u v (chord i)

def step (a : Compact) (c : P) : Compact :=
  let v := next a.1 c
  (v, a.2 + smallBump a.1 v)

def smallEdge (a b : Compact) : Prop := ∃ c : P, step a c = b

private def pathFlow : List B → Lamp B
  | [] => 0
  | [_] => 0
  | u::v::w => bump u v + pathFlow (v::w)

def pot (u : B) : Lamp B := pathFlow (tree u)

def frame (i : Fin 8) (q : B × B) : Z :=
  let (u,v) := chord i
  (pot u) q + bump u v q - (pot v) q

set_option maxRecDepth 30000
set_option maxHeartbeats 0

private theorem anti (u v : B) (q : B × B) : bump v u q = -bump u v q := by
  simp only [bump]
  abel

private theorem flow_extend (w : List B) (u v : B) (h : w.getLast? = some u) (q : B × B) :
    pathFlow (w ++ [v]) q = pathFlow w q + bump u v q := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    cases w with
    | nil =>
      have e : a = u := by simpa using h
      simp [pathFlow,e]
    | cons b w =>
      have h' : (b::w).getLast? = some u := by simpa using h
      change bump a b q + pathFlow ((b::w) ++ [v]) q = _
      rw [ih h']
      simp only [pathFlow, Pi.add_apply, add_assoc]

private theorem tree_last (u : B) : (tree u).getLast? = some u := by decide +revert

private def StepKind (u v : B) : Prop :=
  (∃ i : Fin 8, chord i = (u,v) ∧ ∀ j, smallBump u v j = if i=j then 1 else 0) ∨
  (∃ i : Fin 8, chord i = (v,u) ∧ ∀ j, smallBump u v j = if i=j then -1 else 0) ∨
  ((tree v = tree u ++ [v] ∨ tree u = tree v ++ [u]) ∧ ∀ j, smallBump u v j = 0)

private instance (u v : B) : Decidable (StepKind u v) := by unfold StepKind; infer_instance
private theorem kind (u : B) (c : P) : StepKind u (next u c) := by decide +revert

private theorem node_calc (u : B) (c : P) (q : B × B) :
    pot (next u c) q + ∑ i : Fin 8, smallBump u (next u c) i * frame i q
      = pot u q + bump u (next u c) q := by
  rcases kind u c with ⟨i, hi, eq⟩ | ⟨i, hi, eq⟩ | ⟨paths, eq⟩
  · simp only [eq,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,frame,hi]
    abel
  · simp only [eq,ite_mul,neg_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,frame,hi,anti (next u c) u q]
    abel
  · simp only [eq,zero_mul,Finset.sum_const_zero,add_zero]
    rcases paths with e|e
    · unfold pot
      rw [e,flow_extend _ u (next u c) (tree_last u)]
    · have e' := flow_extend (tree (next u c)) (next u c) u (tree_last _) q
      rw [←e, ←show pot (next u c) q=pathFlow (tree (next u c)) q from rfl, ←show pot u q=pathFlow (tree u) q from rfl, anti u (next u c) q] at e'
      rw [e']
      abel

private theorem pot_zero (u : B) (i : Fin 8) : pot u (chord i) = 0 := by decide +revert

private theorem frame_read (i j : Fin 8) : frame i (chord j) = if i=j then 1 else 0 := by
  decide +revert

def lift (a : Compact) : S₁ :=
  (a.1, fun q => pot a.1 q + ∑ i : Fin 8, a.2 i * frame i q)

private theorem lift_read (a : Compact) (j : Fin 8) : (lift a).2 (chord j) = a.2 j := by
  simp only [lift,pot_zero,zero_add,frame_read,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem lift_inj : Function.Injective lift := by
  intro a b e
  exact Prod.ext (congrArg (Prod.fst : S₁ → B) e) (funext fun j => by
    simpa only [lift_read] using congrArg (fun z : S₁ => z.2 (chord j)) e)

theorem lift_adj {a b : Compact} (h : smallEdge a b) : Full (lift a) (lift b) := by
  obtain ⟨c,rfl⟩ := h
  refine ⟨⟨c,rfl⟩, ?_⟩
  funext q
  have E := node_calc a.1 c q
  simp only [lift,step,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  rw [add_left_comm (pot (next a.1 c) q),E]
  abel

noncomputable def intoLamp (L : Lamp Compact) : Lamp S₁ := by
  classical
  exact fun q => if h : ∃ p : Compact × Compact, (lift p.1,lift p.2) = q then L h.choose else 0

private theorem pair_inj : Function.Injective (fun p : Compact × Compact => (lift p.1,lift p.2)) :=
  fun _ _ e => Prod.ext (lift_inj (congrArg Prod.fst e)) (lift_inj (congrArg Prod.snd e))

@[simp] theorem intoLamp_image (L : Lamp Compact) (u v : Compact) :
    intoLamp L (lift u,lift v) = L (u,v) := by
  classical
  unfold intoLamp
  split
  · rename_i hp
    have hh : hp.choose = (u,v) := pair_inj (a₁:=hp.choose) (a₂:=(u,v)) hp.choose_spec
    rw [hh]
  · rename_i hp
    exact False.elim (hp ⟨(u,v),rfl⟩)

noncomputable def lift₂ (a : Compact × Lamp Compact) : S₂ := (lift a.1, intoLamp a.2)

theorem lift₂_inj : Function.Injective lift₂ := by
  intro a b e
  refine Prod.ext (lift_inj (congrArg Prod.fst e)) ?_
  funext q
  simpa only [lift₂,intoLamp_image] using congrArg (fun z : S₂ => z.2 (lift q.1,lift q.2)) e

theorem lift₂_adj {a b : Compact × Lamp Compact} (h : liftEdge smallEdge a b) :
    Double (lift₂ a) (lift₂ b) := by
  refine ⟨lift_adj h.1, ?_⟩
  funext q
  simp only [lift₂,Pi.add_apply]
  classical
  by_cases hp : ∃ p : Compact × Compact, (lift p.1,lift p.2) = q
  · obtain ⟨⟨u,v⟩, rfl⟩ := hp
    simp only [intoLamp_image, bump, Prod.mk.injEq, lift_inj.eq_iff]
    simpa only [Pi.add_apply, bump, Prod.mk.injEq] using congrArg (fun z : Lamp Compact => z (u,v)) h.2
  · have e₁ : (lift a.1,lift b.1) ≠ q := fun e => hp ⟨(a.1,b.1),e⟩
    have e₂ : (lift b.1,lift a.1) ≠ q := fun e => hp ⟨(b.1,a.1),e⟩
    simp [intoLamp,hp,bump,e₁,e₂]

end HeawoodLift64
