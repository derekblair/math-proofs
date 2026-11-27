import GeometricChargeGraph
import Mathlib.Data.Fintype.Prod

namespace RobustFolkman
open Finset Moment
variable {V : Type*} [DecidableEq V] [Fintype V]

abbrev Tuple5 (V : Type*) := V × V × V × V × V

def tupleEdges (r : Tuple5 V) : EdgeGraph V :=
  forbiddenEdges r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2

def goodTuple (G : EdgeGraph V) (r : Tuple5 V) : Prop :=
  let (u,v,x,y,z) := r
  u≠v ∧ x≠y ∧ z≠x ∧ z≠y ∧ u≠x ∧ u≠y ∧ v≠x ∧ v≠y ∧ u≠z ∧ v≠z ∧ tupleEdges r⊆G

def goodFresh (G : EdgeGraph V) (r : Tuple5 V) (w : V) : Prop :=
  let (u,v,x,y,z) := r
  goodTuple G r ∧ w∉({u,v,x,y,z}:Finset V) ∧ ({u,w}:Finset V)∈G ∧ ({z,w}:Finset V)∈G

noncomputable def labelTuple (G : EdgeGraph V) (H : (forbiddenCopies G : Set (EdgeGraph V))) :
    Tuple5 V :=
  let L := Classical.choice (fiveLabel_of_copy G H.val H.property)
  (L.u,L.v,L.x,L.y,L.z)

omit [Fintype V] in
theorem labelTuple_edges (G : EdgeGraph V) (H : (forbiddenCopies G : Set (EdgeGraph V))) :
    tupleEdges (labelTuple G H)=H.val :=
  (Classical.choice (fiveLabel_of_copy G H.val H.property)).edges_eq.symm

theorem labelTuple_good (G : EdgeGraph V) (H : (forbiddenCopies G : Set (EdgeGraph V))) :
    goodTuple G (labelTuple G H) := by
  let L := Classical.choice (fiveLabel_of_copy G H.val H.property)
  change L.u≠L.v ∧ L.x≠L.y ∧ L.z≠L.x ∧ L.z≠L.y ∧ L.u≠L.x ∧ L.u≠L.y ∧
    L.v≠L.x ∧ L.v≠L.y ∧ L.u≠L.z ∧ L.v≠L.z ∧ tupleEdges (labelTuple G H)⊆G
  rw [labelTuple_edges]
  exact ⟨L.uv,L.xy,L.zx,L.zy,L.ux,L.uy,L.vx,L.vy,L.uz,L.vz,(mem_copies.mp H.property).1⟩

noncomputable def copyIndicator {K : Type*} [Zero K] [One K]
    (G : EdgeGraph V) (r : Tuple5 V) : K := by classical exact if goodTuple G r then 1 else 0

noncomputable def freshIndicator {K : Type*} [Zero K] [One K]
    (G : EdgeGraph V) (rw : Tuple5 V × V) : K := by
  classical exact if goodFresh G rw.1 rw.2 then 1 else 0

/-- Each charged triangle is covered by a canonical five-label tuple
and its third vertex. There are at most three internal choices; fresh
choices contribute a six-label indicator of the attachment pattern. -/
theorem charge_tuple_upper (G : EdgeGraph V) :
    charge (triangles G) (forbiddenCopies G) marked ≤
      3*(∑ r : Tuple5 V, copyIndicator (K:=Nat) G r) +
        ∑ rw : Tuple5 V × V, freshIndicator (K:=Nat) G rw := by
  classical
  let row : Tuple5 V → Nat := fun r =>
    3*copyIndicator (K:=Nat) G r + (univ.filter (goodFresh G r)).card
  have bound :
      ∑ H ∈ (forbiddenCopies G).attach, ((triangles G).filter (fun T => marked H.val∈T)).card ≤
        ∑ r, row r := by
    apply Finset.sum_le_sum_of_injOn (labelTuple G)
    · intro H _ K _ eq
      apply Subtype.ext
      exact (labelTuple_edges G H).symm.trans ((congrArg tupleEdges eq).trans (labelTuple_edges G K))
    · exact subset_univ _
    · intro H _
      have good := labelTuple_good G H
      have h := charge_marked_row G H.val H.property
      let L := Classical.choice (fiveLabel_of_copy G H.val H.property)
      let outside : Finset V := univ.filter (fun w =>
        w∉({L.u,L.v,L.x,L.y,L.z}:Finset V) ∧ {L.u,w}∈G ∧ {L.z,w}∈G)
      have h' : ((triangles G).filter (fun T => marked H.val∈T)).card ≤ 3+outside.card := h
      have filters : univ.filter (goodFresh G (labelTuple G H)) = outside := by
        ext w
        simp only [mem_filter, mem_univ, true_and, outside]
        change goodTuple G (labelTuple G H) ∧ _ ↔ _
        exact ⟨And.right, fun p => ⟨good,p⟩⟩
      change _ ≤ 3*copyIndicator (K:=Nat) G (labelTuple G H) +
        (univ.filter (goodFresh G (labelTuple G H))).card
      rw [show copyIndicator (K:=Nat) G (labelTuple G H)=1 by simp [copyIndicator,good],
        Nat.mul_one,filters]
      exact h'
    · intro _ _ _
      exact Nat.zero_le _
  rw [Finset.sum_attach (forbiddenCopies G) (fun H => ((triangles G).filter (fun T => marked H∈T)).card)] at bound
  unfold charge
  apply bound.trans
  change (∑ r : Tuple5 V, (3*copyIndicator (K:=Nat) G r + (univ.filter (goodFresh G r)).card)) ≤ _
  rw [sum_add_distrib, ←Finset.mul_sum]
  apply le_of_eq
  congr 1
  conv_rhs => rw [←Finset.univ_product_univ,Finset.sum_product]
  apply sum_congr rfl
  intro r _
  rw [Finset.card_filter]
  rfl


variable {Ω K : Type*} [Fintype Ω] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Exact stochastic loss reduction for the actual forbidden graph,
given uniform upper bounds on the two finite labeled probabilities. -/
theorem mean_actual_charge_upper (p : Ω → K) (p0 : ∀ ω, 0≤p ω)
    (G : Ω → EdgeGraph V) (ph pj : K)
    (mh : ∀ r : Tuple5 V, mean p (fun ω => copyIndicator (G ω) r) ≤ ph)
    (mj : ∀ rw : Tuple5 V × V, mean p (fun ω => freshIndicator (G ω) rw) ≤ pj) :
    mean p (fun ω => (charge (triangles (G ω)) (forbiddenCopies (G ω)) marked : K)) ≤
      3*(Fintype.card V : K)^5*ph+(Fintype.card V : K)^6*pj := by
  classical
  have h := expected_charge_upper p p0
    (fun ω => (charge (triangles (G ω)) (forbiddenCopies (G ω)) marked : K))
    (univ : Finset (Tuple5 V)) (univ : Finset (Tuple5 V × V))
    (fun r ω => copyIndicator (G ω) r) (fun rw ω => freshIndicator (G ω) rw)
    3 ph pj (by positivity) ?_ (fun r _ => mh r) (fun rw _ => mj rw)
  · convert h using 1
    simp only [card_univ,Fintype.card_prod,Nat.cast_mul]
    ring
  · intro ω
    have a : ∀ r : Tuple5 V, ((copyIndicator (K:=Nat) (G ω) r : Nat) : K)
        = copyIndicator (G ω) r := by
      intro r
      unfold copyIndicator
      split <;> simp
    have b : ∀ rw : Tuple5 V × V, ((freshIndicator (K:=Nat) (G ω) rw : Nat) : K)
        = freshIndicator (G ω) rw := by
      intro rw
      unfold freshIndicator
      split <;> simp
    have ck : ((charge (triangles (G ω)) (forbiddenCopies (G ω)) marked : Nat) : K) ≤
        ((3*(∑ r : Tuple5 V, copyIndicator (K:=Nat) (G ω) r) +
           ∑ rw : Tuple5 V × V, freshIndicator (K:=Nat) (G ω) rw : Nat) : K) := by
      exact_mod_cast charge_tuple_upper (G ω)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,a,b] using ck

#print axioms charge_tuple_upper
#print axioms mean_actual_charge_upper
end RobustFolkman
