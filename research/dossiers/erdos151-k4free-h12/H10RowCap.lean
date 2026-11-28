import UnblockingPools
import PrivatePools

namespace Erdős151.H10

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : V → V → Prop} (S E : Finset V) (u : V)

def restrict (G : V → V → Prop) (P : Finset V) (x y : V) : Prop :=
  x ∈ P ∧ y ∈ P ∧ G x y

theorem row_cap_h10
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ x, ¬G x x) (link : TriangleFreeLinks G)
    (cap : FreeCap G 9) (hs : Free (Forbidden G) S) (dis : Disjoint S E)
    (blocked : ∀ x ∈ E, ¬ Free (Forbidden G) (insert x ↑S)) (hu : u ∈ S) :
    let P := rowPrivate G S E u
    let Q := rowPrivateLone G S E u
    (S.card = 9 → P.card + Q.card ≤ 2) ∧
    (S.card = 8 → P.card ≤ 5) := by
  classical
  let P := rowPrivate G S E u
  let Q := rowPrivateLone G S E u
  let H := restrict G P
  have symH {a b} (h : H a b) : H b a := ⟨h.2.1, h.1, sym h.2.2⟩
  have irrH (a : V) (h : H a a) : False := irr a h.2.2
  have nb {x : V} (hx : x ∈ P) : G u x := rowPrivate_neighbor (G := G) sym S E dis hs blocked hu hx
  have tfH : Erdos151Ramsey.TriangleFree H :=
    fun a b c hab hbc hac => link u a b c (nb hab.1) (nb hab.2.1) (nb hbc.2.1)
      hab.2.2 hbc.2.2 hac.2.2
  have iso : Erdos151Ramsey.IsolatedIn H Q P :=
    ⟨rowPrivateLone_subset (G := G) S E u, fun _ hx _ hy h =>
      rowPrivateLone_isolated (G := G) sym S E dis hs blocked hu hx hy h.2.2⟩
  have alpha : Erdos151Ramsey.AlphaCap H P (10-S.card) := by
    intro T hT hin
    have subE : T ⊆ E := by
      intro x hx
      exact (Finset.mem_filter.mp (hT hx : x ∈ rowPrivate G S E u)).1
    have dT : Disjoint S T :=
      Finset.disjoint_left.mpr (fun _ hx hy => Finset.disjoint_left.mp dis hx (subE hy))
    have ind : Independence G T :=
      fun a ha b hb _ hab => hin a ha b hb ⟨hT ha,hT hb,hab⟩
    have hp := private_ext_card (G := G) sym cap S T dT hs ind hu
      (fun x hx => (Finset.mem_filter.mp (hT hx : x ∈ rowPrivate G S E u)).2)
    have pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨u,hu⟩
    omega
  refine ⟨?_,?_⟩
  · intro h
    exact Erdos151Ramsey.private_d10 H symH irrH tfH iso (by simpa [h] using alpha)
  · intro h
    have hh := Erdos151Ramsey.private_d9 H symH irrH tfH iso (by simpa [h] using alpha)
    change P.card ≤ 5
    omega

#print axioms row_cap_h10
end Erdős151.H10
