import Mathlib.Algebra.Group.Basic
import Lean.Elab.Tactic.Omega

namespace GenericVoltage

variable {B A X : Type*} [AddCommGroup A]
variable {R : B → B → Prop}

def Adj (R : B → B → Prop) (W : B → B → A) (u v : B × A) : Prop :=
  R u.1 v.1 ∧ u.2 + W u.1 v.1 = v.2

def Cycle {X : Type*} (R : X → X → Prop) (n : Nat) : Prop :=
  ∃ v : Fin n → X, Function.Injective v ∧
    ∀ i, R (v i) (v ⟨(i.val+1)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

def cycSucc {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

theorem lift_of_rows (W : B → B → A) {n : Nat} (f : Fin n → B) (p : Fin n → A)
    (edge : ∀ i, R (f i) (f (cycSucc i)))
    (step : ∀ i, p i + W (f i) (f (cycSucc i)) = p (cycSucc i))
    (sep : ∀ i j, i≠j → f i=f j → p i≠p j) :
    Cycle (Adj R W) n := by
  refine ⟨fun i => (f i,p i), ?_, fun i => ⟨edge i,step i⟩⟩
  intro i j eq
  by_contra h
  exact sep i j h (congrArg Prod.fst eq) (congrArg Prod.snd eq)

def prefixVoltage (W : B → B → A) (p : Nat → B) : Nat → A
  | 0 => 0
  | k+1 => prefixVoltage W p k + W (p k) (p (k+1))

/-- A simple cycle in the voltage graph follows from a closed base walk whose
prefix voltages separate all internal visits to each base vertex. -/
theorem lift_of_prefix (W : B → B → A) (p : Nat → B) {n : Nat}
    (edge : ∀ i<n, R (p i) (p (i+1)))
    (closed : p n = p 0) (zero : prefixVoltage W p n = 0)
    (sep : ∀ i j, i<n → j<n → i≠j → p i=p j → prefixVoltage W p i ≠ prefixVoltage W p j) :
    Cycle (Adj R W) n := by
  let f : Fin n → B × A := fun i => (p i.val, prefixVoltage W p i.val)
  refine ⟨f,?_,?_⟩
  · intro i j eq
    apply Fin.ext
    by_contra hn
    exact sep i.val j.val i.isLt j.isLt hn (congrArg Prod.fst eq) (congrArg Prod.snd eq)
  · intro i
    change Adj R W (p i.val,prefixVoltage W p i.val)
      (p ((i.val+1)%n),prefixVoltage W p ((i.val+1)%n))
    have h : Adj R W (p i.val,prefixVoltage W p i.val) (p (i.val+1),prefixVoltage W p (i.val+1)) :=
      ⟨edge i.val i.isLt,rfl⟩
    by_cases i' : i.val+1<n
    · simpa [Nat.mod_eq_of_lt i'] using h
    · have eq : i.val+1=n := by omega
      rw [eq,Nat.mod_self]
      rw [eq,closed,zero] at h
      exact h

/-- A cover of a graph on `B`, with a free and transitive additive deck action
on every fiber. No finiteness or connectedness of the covering graph is required. -/
structure RegularAbelianCover (B A X : Type*) [AddCommGroup A] (R : B → B → Prop) where
  adj : X → X → Prop
  symm : ∀ {u v}, adj u v → adj v u
  proj : X → B
  onto : Function.Surjective proj
  act : A → X → X
  zero_act : ∀ u, act 0 u = u
  add_act : ∀ a b u, act (a+b) u = act a (act b u)
  fiber_pres : ∀ a u, proj (act a u) = proj u
  edge_pres : ∀ a {u v}, adj u v → adj (act a u) (act a v)
  fiber_torsor : ∀ {u v}, proj u = proj v → ∃! a, act a u = v
  edge_proj : ∀ {u v}, adj u v → R (proj u) (proj v)
  edge_lift : ∀ u b, R (proj u) b → ∃! v, proj v = b ∧ adj u v

namespace RegularAbelianCover

variable (C : RegularAbelianCover B A X R)

noncomputable def rep (u : B) : X := Classical.choose (C.onto u)

@[simp] theorem rep_spec (u : B) : C.proj (C.rep u) = u :=
  Classical.choose_spec (C.onto u)

private theorem deck_unique {a b : A} {u v : X}
    (ha : C.act a u = v) (hb : C.act b u = v) : a = b := by
  have e : C.proj u = C.proj v := by rw [← ha, C.fiber_pres]
  obtain ⟨z, _, hz⟩ := C.fiber_torsor e
  exact (hz a ha).trans (hz b hb).symm

noncomputable def chart (s : B × A) : X := C.act s.2 (C.rep s.1)

@[simp] theorem chart_proj (s : B × A) : C.proj (C.chart s) = s.1 := by
  simp [chart, C.fiber_pres]

theorem chart_injective : Function.Injective C.chart := by
  intro s t H
  have eq : s.1 = t.1 := by simpa using congrArg C.proj H
  apply Prod.ext eq
  change C.act s.2 (C.rep s.1) = C.act t.2 (C.rep t.1) at H
  rw [← eq] at H
  exact C.deck_unique H rfl

include C in
private theorem edge_symm {u v : B} (e : R u v) :
    R v u := by
  have E : R (C.proj (C.rep u)) v := by simpa using e
  obtain ⟨x, ⟨hx, ax⟩, _⟩ := C.edge_lift (C.rep u) v E
  simpa [hx] using C.edge_proj (C.symm ax)

private theorem localDeck (u v : B) (E : R u v) :
    ∃ a, C.adj (C.rep u) (C.act a (C.rep v)) := by
  have E' : R (C.proj (C.rep u)) v := by simpa using E
  obtain ⟨x, ⟨hx, ax⟩, _⟩ := C.edge_lift (C.rep u) v E'
  have e : C.proj (C.rep v) = C.proj x := by simp [hx]
  obtain ⟨a, ha, _⟩ := C.fiber_torsor e
  exact ⟨a, ha ▸ ax⟩

noncomputable def voltage (u v : B) : A := by
  classical
  exact if E : R u v then Classical.choose (C.localDeck u v E) else 0

theorem voltage_edge {u v : B} (E : R u v) :
    C.adj (C.rep u) (C.act (C.voltage u v) (C.rep v)) := by
  unfold voltage
  rw [dite_eq_left E]
  exact Classical.choose_spec (C.localDeck u v E)

theorem voltage_antisymm (u v : B) : C.voltage v u = -C.voltage u v := by
  by_cases E : R u v
  · have E' := C.edge_symm E
    have a := C.voltage_edge E
    have b := C.voltage_edge E'
    let d := C.voltage u v
    have rb : C.adj (C.rep v) (C.act (-d) (C.rep u)) := by
      have H := C.edge_pres (-d) (C.symm a)
      change C.adj (C.act (-d) (C.act d (C.rep v))) _ at H
      rwa [← C.add_act, neg_add_cancel, C.zero_act] at H
    have E'' : R (C.proj (C.rep v)) u := by simpa using E'
    obtain ⟨z, _, hz⟩ := C.edge_lift (C.rep v) u E''
    apply C.deck_unique (v := z)
    · exact hz _ ⟨by rw [C.fiber_pres, C.rep_spec], b⟩
    · exact hz _ ⟨by rw [C.fiber_pres, C.rep_spec], rb⟩
  · have E' : ¬ R v u := fun h => E (C.edge_symm h)
    simp [voltage, E, E']

theorem chart_adj {s t : B × A} (E : Adj R C.voltage s t) :
    C.adj (C.chart s) (C.chart t) := by
  obtain ⟨hj, h⟩ := E
  have H := C.edge_pres s.2 (C.voltage_edge hj)
  rwa [← C.add_act, h] at H


theorem chart_surjective : Function.Surjective C.chart := by
  intro u
  have h : C.proj (C.rep (C.proj u)) = C.proj u := C.rep_spec _
  obtain ⟨a,ha,_⟩ := C.fiber_torsor h
  exact ⟨(C.proj u,a),ha⟩

theorem chart_adj_iff {s t : B × A} :
    C.adj (C.chart s) (C.chart t) ↔ Adj R C.voltage s t := by
  constructor
  · intro h
    have E : R s.1 t.1 := by simpa using C.edge_proj h
    refine ⟨E,?_⟩
    have N := C.edge_pres s.2 (C.voltage_edge E)
    rw [← C.add_act] at N
    have E' : R (C.proj (C.chart s)) t.1 := by
      simpa using E
    obtain ⟨z,_,hz⟩ := C.edge_lift (C.chart s) t.1 E'
    apply C.deck_unique (u := C.rep t.1) (v := z)
    · exact hz _ ⟨by rw [C.fiber_pres, C.rep_spec],N⟩
    · exact hz _ ⟨C.chart_proj t,h⟩
  · exact C.chart_adj

theorem cycle_transport {n : Nat} (h : Cycle (Adj R C.voltage) n) : Cycle C.adj n := by
  obtain ⟨f,fi,fa⟩ := h
  exact ⟨C.chart ∘ f, C.chart_injective.comp fi, fun i => C.chart_adj (fa i)⟩

theorem prefix_transport (p : Nat → B) {n : Nat}
    (edge : ∀ i<n, R (p i) (p (i+1)))
    (closed : p n = p 0) (zero : prefixVoltage C.voltage p n = 0)
    (sep : ∀ i j, i<n → j<n → i≠j → p i=p j →
      prefixVoltage C.voltage p i ≠ prefixVoltage C.voltage p j) :
    Cycle C.adj n :=
  C.cycle_transport (lift_of_prefix C.voltage p edge closed zero sep)

end RegularAbelianCover
end GenericVoltage
#print axioms GenericVoltage.lift_of_rows
#print axioms GenericVoltage.lift_of_prefix
#print axioms GenericVoltage.RegularAbelianCover.voltage_antisymm
#print axioms GenericVoltage.RegularAbelianCover.prefix_transport
#print axioms GenericVoltage.RegularAbelianCover.chart_adj_iff
