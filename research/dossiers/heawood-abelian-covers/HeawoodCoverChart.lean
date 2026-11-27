import HeawoodAbelian

namespace HeawoodCoverChart

open HaarOrbitC7Voltage

variable {A X : Type*} [AddCommGroup A]

/-- A cover of the Heawood graph, with a free and transitive additive deck action
on every fiber. No finiteness or connectedness of the covering graph is required. -/
structure RegularAbelianCover (A X : Type*) [AddCommGroup A] where
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
  edge_proj : ∀ {u v}, adj u v → ∃ j, next (proj u) j = proj v
  edge_lift : ∀ u b, (∃ j, next (proj u) j = b) → ∃! v, proj v = b ∧ adj u v

namespace RegularAbelianCover

variable (C : RegularAbelianCover A X)

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
private theorem edge_symm {u v : B} (e : ∃ j, next u j = v) :
    ∃ j, next v j = u := by
  have E : ∃ j, next (C.proj (C.rep u)) j = v := by simpa using e
  obtain ⟨x, ⟨hx, ax⟩, _⟩ := C.edge_lift (C.rep u) v E
  simpa [hx] using C.edge_proj (C.symm ax)

private theorem localDeck (u v : B) (E : ∃ j, next u j = v) :
    ∃ a, C.adj (C.rep u) (C.act a (C.rep v)) := by
  have E' : ∃ j, next (C.proj (C.rep u)) j = v := by simpa using E
  obtain ⟨x, ⟨hx, ax⟩, _⟩ := C.edge_lift (C.rep u) v E'
  have e : C.proj (C.rep v) = C.proj x := by simp [hx]
  obtain ⟨a, ha, _⟩ := C.fiber_torsor e
  exact ⟨a, ha ▸ ax⟩

noncomputable def voltage (u v : B) : A := by
  classical
  exact if E : ∃ j, next u j = v then Classical.choose (C.localDeck u v E) else 0

theorem voltage_edge {u v : B} (E : ∃ j, next u j = v) :
    C.adj (C.rep u) (C.act (C.voltage u v) (C.rep v)) := by
  unfold voltage
  rw [dite_eq_left E]
  exact Classical.choose_spec (C.localDeck u v E)

theorem voltage_antisymm (u v : B) : C.voltage v u = -C.voltage u v := by
  by_cases E : ∃ j, next u j = v
  · have E' := C.edge_symm E
    have a := C.voltage_edge E
    have b := C.voltage_edge E'
    let d := C.voltage u v
    have rb : C.adj (C.rep v) (C.act (-d) (C.rep u)) := by
      have H := C.edge_pres (-d) (C.symm a)
      change C.adj (C.act (-d) (C.act d (C.rep v))) _ at H
      rwa [← C.add_act, neg_add_cancel, C.zero_act] at H
    have E'' : ∃ j, next (C.proj (C.rep v)) j = u := by simpa using E'
    obtain ⟨z, _, hz⟩ := C.edge_lift (C.rep v) u E''
    apply C.deck_unique (v := z)
    · exact hz _ ⟨by rw [C.fiber_pres, C.rep_spec], b⟩
    · exact hz _ ⟨by rw [C.fiber_pres, C.rep_spec], rb⟩
  · have E' : ¬ ∃ j, next v j = u := fun h => E (C.edge_symm h)
    simp [voltage, E, E']

theorem chart_adj {s t : B × A} (E : HaarOrbitC7RealCover.Adj C.voltage s t) :
    C.adj (C.chart s) (C.chart t) := by
  obtain ⟨_, j, hj, h⟩ := E
  have H := C.edge_pres s.2 (C.voltage_edge ⟨j,hj⟩)
  rwa [← C.add_act, h] at H

def HasCycle (n : Nat) : Prop :=
  ∃ f : Fin n → X, Function.Injective f ∧
    ∀ i, C.adj (f i) (f ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem dyadic_cycle : ∃ n, n ∈ [8,16,32] ∧ C.HasCycle n := by
  obtain ⟨n,hn,f,fi,fa⟩ :=
    HeawoodCert.every_regular_abelian_voltage C.voltage C.voltage_antisymm
  exact ⟨n, hn, C.chart ∘ f, C.chart_injective.comp fi, fun i => C.chart_adj (fa i)⟩

end RegularAbelianCover
end HeawoodCoverChart

#print axioms HeawoodCoverChart.RegularAbelianCover.dyadic_cycle
