import SimpleWagnerColor
import MinimalCoreConnected

namespace Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty edge-minimal Ramsey core cannot have a Wagner link at
every nonisolated vertex. Isolates in the ambient vertex type are removed
only for the coloring step. -/
theorem minimal_locally_wagner_impossible (C : V → V → Prop)
    (sym : BikovLocal.Sym C) (irr : BikovLocal.Loopless C)
    (ramsey : BikovLocal.Ramsey C)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H C → BikovLocal.Sym H →
      ∀ a b, C a b → ¬H a b → ¬BikovLocal.Ramsey H)
    (nonempty : ∃ a b,C a b)
    (iso : ∀ w, (∃ v,C w v) →
      ∃ e : Fin 8 ≃ {x : V // x≠w ∧ C w x},
        ∀ i j, WagnerFin8.Adj i j ↔ C (e i).val (e j).val) : False := by
  classical
  let W := CoreSupp C
  letI : Fintype W := by
    change Fintype {v : V // ∃ u,C v u}
    infer_instance
  let J : SimpleGraph W := asSimple (CoreAdj C) (fun h => sym h) (fun a h => irr a.val h)
  have supp (w : W) (x : {x : V // x≠w.val ∧ C w.val x}) : ∃ q,C x.val q :=
    ⟨w.val,sym x.property.2⟩
  let lift (w : W) : {x : V // x≠w.val ∧ C w.val x}
      ≃ {x : W // x≠w ∧ J.Adj w x} :=
    { toFun := fun x => ⟨⟨x.val,supp w x⟩,⟨fun h => x.property.1 (congrArg Subtype.val h),x.property.2⟩⟩
      invFun := fun x => ⟨x.val.val,⟨fun h => x.property.1 (Subtype.ext h), x.property.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have jiso (w : W) : ∃ e : Fin 8 ≃ {x : W // x≠w ∧ J.Adj w x},
      ∀ i j, WagnerFin8.Adj i j ↔ J.Adj (e i).val (e j).val := by
    obtain ⟨m,hm⟩ := iso w.val w.property
    exact ⟨m.trans (lift w),hm⟩
  obtain ⟨a,b,ab⟩ := nonempty
  let p : W := ⟨a,⟨b,ab⟩⟩
  have jconn : ∀ a b : W, Relation.ReflTransGen J.Adj a b :=
    support_connected C sym ramsey minimal
  obtain ⟨c,cs,good⟩ := actual_locally_wagner_safe J p jconn jiso
  exact restrict_ramsey_to_support C sym ramsey c cs good

#print axioms minimal_locally_wagner_impossible
end Erdős151.H12
