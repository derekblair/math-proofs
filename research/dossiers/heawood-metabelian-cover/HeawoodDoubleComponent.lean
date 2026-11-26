import HeawoodDoubleCover
import Mathlib.GroupTheory.Coset.Card

namespace HeawoodDoubleComponent

open HeawoodDouble HeawoodDoubleDeck HaarDerivedFlowPositive
open HaarOrbitC7Voltage (B P next)
open Relation (ReflTransGen)

private theorem reach_map {X Y : Type*} {r : X → X → Prop} {s : Y → Y → Prop}
    (f : X → Y) (hom : ∀ {x y}, r x y → s (f x) (f y)) {u v : X}
    (h : ReflTransGen r u v) : ReflTransGen s (f u) (f v) := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (hom e)

private theorem reach_reverse {X : Type*} {r : X → X → Prop}
    (symm : ∀ {x y}, r x y → r y x) {u v : X}
    (h : ReflTransGen r u v) : ReflTransGen r v u := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.head (symm e)

theorem edge_symm {u v : V2} (e : Edge2 u v) : Edge2 v u :=
  HomologyThree.liftSymm Edge1 (HomologyThree.liftSymm HeawoodGirthSix.Edge HeawoodGirthSix.symm) e

abbrev Reach := ReflTransGen Edge2

theorem act_reach (d : Deck) {u v : V2} (e : Reach u v) :
    Reach (action d u) (action d v) :=
  reach_map (action d) (fun e => action_edge d e) e

def stabilizer (o : V2) : Subgroup Deck where
  carrier := {d | Reach o (action d o)}
  one_mem' := by change Reach o (action 1 o); rw [action_one]
  mul_mem' := by
    intro a b ha hb
    change Reach o (action (a*b) o)
    rw [action_mul]
    exact ha.trans (act_reach a hb)
  inv_mem' := by
    intro a ha
    change Reach o (action a⁻¹ o)
    have h := act_reach a⁻¹ ha
    rw [← action_mul, inv_mul_cancel, action_one] at h
    exact reach_reverse edge_symm h

abbrev Component (o : V2) := {u : V2 // Reach o u}

def adj {o : V2} (u v : Component o) : Prop := Edge2 u.val v.val

def proj {o : V2} (u : Component o) : B := base u.val

def act {o : V2} (d : stabilizer o) (u : Component o) : Component o :=
  ⟨action d.val u.val, (show Reach o (action d.val o) from d.property).trans
    (act_reach d.val u.property)⟩

theorem act_one {o : V2} (u : Component o) : act 1 u = u :=
  Subtype.ext (action_one u.val)

theorem act_mul {o : V2} (a b : stabilizer o) (u : Component o) :
    act (a*b) u = act a (act b u) := Subtype.ext (action_mul a.val b.val u.val)

theorem act_edges {o : V2} (d : stabilizer o) {u v : Component o}
    (e : adj u v) : adj (act d u) (act d v) := action_edge d.val e

theorem act_projects {o : V2} (d : stabilizer o) (u : Component o) :
    proj (act d u) = proj u := rfl

theorem act_regular {o : V2} (u v : Component o) (h : proj u = proj v) :
    ∃! d : stabilizer o, act d u = v := by
  obtain ⟨d,hd,unique⟩ := action_regular u.val v.val h
  have stab : d ∈ stabilizer o := by
    change Reach o (action d o)
    have H := act_reach d (reach_reverse edge_symm u.property)
    rw [hd] at H
    exact v.property.trans H
  exact ⟨⟨d,stab⟩, Subtype.ext hd,
    fun a ha => Subtype.ext (unique a.val (congrArg Subtype.val ha))⟩

theorem project_adj {o : V2} {u v : Component o} (e : adj u v) :
    HeawoodGirthSix.Edge (proj u) (proj v) := edge_to_base e

theorem unique_lift {o : V2} (u : Component o) (b : B)
    (e : HeawoodGirthSix.Edge (proj u) b) : ∃! v : Component o, adj u v ∧ proj v = b := by
  obtain ⟨v,⟨hv,hb⟩,unique⟩ := HeawoodDoubleDeck.unique_lift u.val b e
  exact ⟨⟨v,u.property.tail hv⟩,⟨hv,hb⟩,fun w hw => Subtype.ext (unique w.val hw)⟩

private def travel : B → List P → B
  | u, [] => u
  | u, j::w => travel (next u j) w

private theorem reach_travel (u : B) (w : List P) :
    ReflTransGen HeawoodGirthSix.Edge u (travel u w) := by
  induction w generalizing u with
  | nil => exact .refl
  | cons j w ih => exact (ih (next u j)).head ⟨j,rfl⟩

private def route (b : B) : List P :=
  (List.replicate (b.val % 7) [1,0]).flatten ++ (if b.val < 7 then [] else [0])

private theorem route_ok : ∀ b : B, travel 0 (route b) = b := by decide +kernel

theorem base_connected (u v : B) : ReflTransGen HeawoodGirthSix.Edge u v := by
  have hu := reach_travel 0 (route u)
  have hv := reach_travel 0 (route v)
  rw [route_ok] at hu hv
  exact (reach_reverse HeawoodGirthSix.symm hu).trans hv

theorem onto (o : V2) : Function.Surjective (@proj o) := by
  intro b
  have H := base_connected (base o) b
  induction H with
  | refl => exact ⟨⟨o,.refl⟩,rfl⟩
  | tail _ e ih =>
      obtain ⟨u,hu⟩ := ih
      rw [← hu] at e
      obtain ⟨v,⟨_,hv⟩,_⟩ := unique_lift u _ e
      exact ⟨v,hv⟩

theorem connected (o : V2) (u v : Component o) : ReflTransGen adj u v := by
  let z : Component o := ⟨o,.refl⟩
  have h (y : Component o) : ReflTransGen adj z y := by
    obtain ⟨y,hy⟩ := y
    induction hy with
    | refl => exact .refl
    | tail hy e ih => exact ih.tail e
  exact (reach_reverse (fun e => edge_symm e) (h u)).trans (h v)

theorem odd_deck (o : V2) : Odd (Nat.card (stabilizer o)) := by
  obtain ⟨k,hk⟩ := Subgroup.card_subgroup_dvd_card (stabilizer o)
  have h := finite_odd
  rw [hk, Nat.odd_mul] at h
  exact h.1

theorem metabelian_deck (o : V2) :
    ∀ a b : commutator (stabilizer o), a*b = b*a := by
  intro a b
  let f := (stabilizer o).subtype
  have h : commutator (stabilizer o) ≤ (projection.comp f).ker :=
    Abelianization.commutator_subset_ker (projection.comp f)
  apply Subtype.ext
  apply Subtype.ext
  exact kernel_comm _ _ (h a.property) (h b.property)

theorem cycles_iff (o : V2) (n : Nat) (hn : 0<n) :
    Cyclic (@adj o) n ↔ Cyclic Edge2 n := by
  constructor
  · rintro ⟨v,vi,ve⟩
    exact ⟨Subtype.val ∘ v,fun _ _ h => vi (Subtype.ext h),ve⟩
  · rintro ⟨v,vi,ve⟩
    let first : Fin n := ⟨0,hn⟩
    obtain ⟨u,hu⟩ := onto o (base (v first))
    obtain ⟨d,hd,_⟩ := action_regular (v first) u.val hu.symm
    have moveInj : Function.Injective (action d) := by
      intro a b eq
      have H := congrArg (action d⁻¹) eq
      simpa only [← action_mul,inv_mul_cancel, action_one] using H
    let w := action d ∘ v
    have root : Reach o (w first) := by
      change Reach o (action d (v first))
      rw [hd]
      exact u.property
    have ew (i : Fin n) : Edge2 (w i) (w ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩) :=
      action_edge d (ve i)
    have cover (j : Nat) (hj : j<n) : Reach o (w ⟨j,hj⟩) := by
      induction j with
      | zero => exact root
      | succ j ih =>
        have E := ew ⟨j, by omega⟩
        have idx : (⟨(j+1)%n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j+1,hj⟩ :=
          Fin.ext (Nat.mod_eq_of_lt hj)
        rw [idx] at E
        exact (ih (by omega)).tail E
    exact ⟨fun i => ⟨w i, cover i.val i.isLt⟩,
      fun _ _ e => vi (moveInj (congrArg Subtype.val e)),ew⟩

end HeawoodDoubleComponent

#print axioms HeawoodDoubleComponent.act_regular
#print axioms HeawoodDoubleComponent.onto
#print axioms HeawoodDoubleComponent.connected
#print axioms HeawoodDoubleComponent.odd_deck
#print axioms HeawoodDoubleComponent.metabelian_deck
#print axioms HeawoodDoubleComponent.cycles_iff
