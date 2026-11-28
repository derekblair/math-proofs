import MarkedLinkTable
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos151CoreHigh
open Erdos151MarkedLinkTable

variable {V : Type*} [DecidableEq V]
variable (N : V→Finset V) (B : V→V→ℕ)

/-- A link identified with one of Bikov's seven marked links. -/
structure NamedLink (w : V) where
  kind : Fin 7
  emb : Fin 8 ↪ V
  vertices : Finset.univ.map emb = N w
  book : ∀ i, B w (emb i)=deg kind i
  induced : ∀ i j, (emb j ∈ N (emb i)) ↔ adj kind i j=true

theorem NamedLink.mem (w : V) (L : NamedLink N B w) (i : Fin 8) : L.emb i∈N w := by
  rw [←L.vertices]
  exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem NamedLink.get (w : V) (L : NamedLink N B w) {z : V}
    (hz : z∈N w) : ∃ i, L.emb i=z := by
  rw [←L.vertices] at hz
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hz
  exact ⟨i,hi⟩

/-- A set of at most three exceptional vertices containing both hubs
contains no two distinct normal vertices. -/
theorem exceptional_pair (X : Finset V) (u v w z : V) (hX : X.card≤3)
    (huv : u≠v) (hu : u∈X) (hv : v∈X) (hw : w∈X) (hz : z∈X)
    (hwu : w≠u) (hwv : w≠v) (hzu : z≠u) (hzv : z≠v)
    (hzw : z≠w) : False := by
  let F : Finset V := {u,v,w,z}
  have hsub : F⊆X := by
    intro a ha
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  have hcard : F.card=4 := by
    have e1 : u∉({v,w,z}:Finset V) := by simp [huv,Ne.symm hwu,Ne.symm hzu]
    have e2 : v∉({w,z}:Finset V) := by simp [Ne.symm hwv,Ne.symm hzv]
    have e3 : w∉({z}:Finset V) := by simp [Ne.symm hzw]
    dsimp [F]
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3]
    simp
  omega

/-- With at most one exceptional non-hub, high booksize is confined to
the edge between the two adjacent hubs. No degree-nine link census. -/
theorem no_high_at_normal (u v : V) (X : Finset V)
    (huv : u≠v) (ha : v∈N u) (hsym : ∀ a b, b∈N a ↔ a∈N b)
    (hloop : ∀ a, a∉N a)
    (hX : X.card≤3) (hu : u∈X) (hv : v∈X)
    (highX : ∀ a b, b∈N a → 4≤B a b → a∈X ∧ b∈X)
    (w z : V) (hwu : w≠u) (hwv : w≠v) (L : NamedLink N B w)
    (hz : z∈N w) : B w z≤3 := by
  by_contra! h
  have hb : 4≤B w z := by omega
  obtain ⟨hwX,hzX⟩ := highX w z hz hb
  have hzw : z≠w := by intro he; exact hloop w (by simpa [he] using hz)
  have hzHub : z=u ∨ z=v := by
    by_contra! H
    exact exceptional_pair X u v w z hX huv hu hv hwX hzX hwu hwv H.1 H.2 hzw
  obtain ⟨i,hi⟩ := NamedLink.get N B w L hz
  have hdeg : 4≤deg L.kind i := by rwa [←L.book i, hi]
  obtain ⟨j,hji,hdegj⟩ := highMate L.kind i hdeg
  let y := L.emb j
  have hym := NamedLink.mem N B w L j
  change y∈N w at hym
  have hyX := (highX w y hym (by change 4≤B w (L.emb j); rwa [L.book j])).2
  have hyw : y≠w := by intro hy; exact hloop w (by simpa [hy] using hym)
  have hyz : y≠z := by
    intro hy
    apply hji
    exact L.emb.injective (hy.trans hi.symm)
  have hyHub : y=u ∨ y=v := by
    by_contra! H
    exact exceptional_pair X u v w y hX huv hu hv hwX hyX hwu hwv H.1 H.2 hyw
  have hxy : y∈N z := by
    rcases hzHub with hzu | hzv <;> rcases hyHub with hyu | hyv
    · exact False.elim (hyz (hyu.trans hzu.symm))
    · simpa [hzu,hyv] using ha
    · simpa [hzv,hyu] using (hsym u v).mp ha
    · exact False.elim (hyz (hyv.trans hzv.symm))
  have hxy' : L.emb j∈N (L.emb i) := by rw [hi]; exact hxy
  exact highIndependent L.kind i j ((L.induced i j).mp hxy') hdeg hdegj

#print axioms no_high_at_normal
end Erdos151CoreHigh
