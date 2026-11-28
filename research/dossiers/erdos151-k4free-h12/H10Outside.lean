import H10RowCap

namespace Erdős151.H10
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem h10_outside_lower {G : V → V → Prop}
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ x, ¬ G x x) (link : TriangleFreeLinks G)
    (cap : FreeCap G 9) (S E : Finset V) (dis : Disjoint S E)
    (hs : Free (Forbidden G) S)
    (hb : ∀ x ∈ E, ¬ Free (Forbidden G) (insert x ↑S)) :
    let I := ∑ x ∈ E, (ns (G := G) S x).card
    let L := ∑ x ∈ E, (ls (G := G) S x).card
    (S.card = 9 → 12*E.card ≤ 4*I+54+2*L) ∧
    (S.card = 8 → L=0 → 6*E.card ≤ 2*I+40) := by
  classical
  let s := fun x => (ns (G := G) S x).card
  let l := fun x => (ls (G := G) S x).card
  let p := fun x => (ps (G := G) S x).card
  let q := fun x => (qs (G := G) S x).card
  let P := fun u x => u ∈ ps (G := G) S x
  let Q := fun u x => u ∈ qs (G := G) S x
  have trans (A B K : ℕ) (hh : ∀ u ∈ S,
      A*(rowPrivate G S E u).card+B*(rowPrivateLone G S E u).card ≤ K) :
      (∑ x ∈ E, (A*p x+B*q x)) ≤ S.card*K := by
    have hp (x : V) : colCount S P x = p x := by
      unfold colCount p
      congr 1
      ext u
      constructor
      · intro hu
        exact (Finset.mem_filter.mp hu).2
      · intro hu
        exact Finset.mem_filter.mpr ⟨((mem_ps (G := G) S x).mp hu).1,hu⟩
    have hq (x : V) : colCount S Q x = q x := by
      unfold colCount q
      congr 1
      ext u
      constructor
      · intro hu
        exact (Finset.mem_filter.mp hu).2
      · intro hu
        exact Finset.mem_filter.mpr ⟨((mem_qs (G := G) S x).mp hu).1,hu⟩
    apply incidence_budget S E P Q A B K
    · intro x _
      rw [hp,hq]
    · exact hh
  have hc x (hx : x ∈ E) := blocked_graph_charge (G := G) S x sym irr hs (hb x hx)
  change (S.card = 9 → 12*E.card ≤ 4*(∑ x ∈ E, s x)+54+2*(∑ x ∈ E, l x)) ∧
    (S.card = 8 → (∑ x ∈ E, l x)=0 → 6*E.card ≤ 2*(∑ x ∈ E, s x)+40)
  refine ⟨?_,?_⟩
  · intro hd
    have hP := trans 1 1 2 (fun u hu => by simpa using
      (row_cap_h10 (G := G) S E u sym irr link cap hs dis hb hu).1 hd)
    have h := sum_charges E s (fun x => p x+q x) l 12 4 3 2 (fun x hx => (hc x hx).1.1)
    rw [hd] at hP
    simp only [one_mul] at hP
    omega
  · intro hd hz
    have hP := trans 1 0 5 (fun u hu => by simpa using
      (row_cap_h10 (G := G) S E u sym irr link cap hs dis hb hu).2 hd)
    have h := sum_charges E s p l 6 2 1 0 (by
      intro x hx
      have hxle : l x ≤ ∑ x ∈ E, l x :=
        Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) hx
      have hx0 : l x = 0 := by omega
      have h1 := (hc x hx).2 hx0
      change 6 ≤ 2*s x+p x at h1
      omega)
    rw [hd] at hP
    simp only [one_mul, zero_mul, add_zero] at hP
    omega

#print axioms h10_outside_lower
end Erdős151.H10
