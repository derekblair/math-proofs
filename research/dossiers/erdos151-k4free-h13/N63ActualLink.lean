import N63ChartBudget

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

def actualLinkDegree (w x : V) : ℕ :=
  ((neighbors G x) ∩ (neighbors C w)).card

theorem actual_link_price_interval (w x : V)
    (sub : ∀ a b, C a b → G a b) :
    let a := (neighbors G x∩neighbors G w).card
    actualLinkDegree G C w x ≤ a ∧
    a ≤ actualLinkDegree G C w x + ((neighbors G w).card - (neighbors C w).card) := by
  dsimp only
  let A := neighbors G x∩neighbors G w
  let B := neighbors G x∩neighbors C w
  let U := neighbors G w
  let S := neighbors C w
  have su : S ⊆ U := fun v hv => (mem_neighbors G).mpr (sub w v ((mem_neighbors C).mp hv))
  have ba : B ⊆ A := fun v hv => Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hv).1,su (Finset.mem_inter.mp hv).2⟩
  have dab : A \ B ⊆ U \ S := by
    intro v hv
    obtain ⟨av,bv⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨xv,wv⟩ := Finset.mem_inter.mp av
    exact Finset.mem_sdiff.mpr ⟨wv,fun s => bv (Finset.mem_inter.mpr ⟨xv,s⟩)⟩
  have p := Finset.card_sdiff_add_card_eq_card ba
  have q := Finset.card_sdiff_add_card_eq_card su
  have z := Finset.card_le_card dab
  change B.card ≤ A.card ∧ A.card ≤ B.card+(U.card-S.card)
  omega

theorem actual_center_witness (w x y : V) (A : Finset V)
    (sub : ∀ a b, C a b → G a b)
    (vA : ∀ v ∈ A, C w v ∧ v ≠ x ∧ v ≠ y ∧ ¬ G x v ∧ ¬ G y v) :
    A ⊆ centerCandidates G C x w y := by
  intro v hv
  obtain ⟨wv,nx,ny,xv,yv⟩ := vA v hv
  refine Finset.mem_sdiff.mpr ⟨(mem_neighbors C).mpr wv,?_⟩
  intro h
  rcases Finset.mem_union.mp h with h|h
  · rcases Finset.mem_union.mp h with h|h
    · exact xv ((mem_neighbors G).mp (Finset.mem_inter.mp h).1)
    · exact yv ((mem_neighbors G).mp (Finset.mem_inter.mp h).1)
  · simpa [nx,ny] using h

theorem free13_of_local_chart
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (Csym : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (cwx : C w x) (cwy : C w y) (hxy : ¬ G x y) (xyne : x ≠ y)
    (rx : 8 ≤ (neighbors C x).card) (ry : 8 ≤ (neighbors C y).card)
    (A : Finset V) (vA : ∀ v ∈ A, C w v ∧ v ≠ x ∧ v ≠ y ∧ ¬ G x v ∧ ¬ G y v)
    (ia : Independent G A) (n : 63 ≤ Fintype.card V)
    (d : (neighbors G x).card + (neighbors G y).card + (neighbors G w).card ≤ D)
    (sx : (neighbors G x).card ≤ 12)
    (p : ∀ a b s : ℕ,
      actualLinkDegree G C w x ≤ a →
      a ≤ actualLinkDegree G C w x + ((neighbors G w).card - (neighbors C w).card) →
      actualLinkDegree G C w y ≤ b →
      b ≤ actualLinkDegree G C w y + ((neighbors G w).card - (neighbors C w).card) →
      s ≤ 12 → D+40 ≤ 63+a+b+s+A.card+outerFloor a b s) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  have a := actual_link_price_interval G C w x sub
  have b := actual_link_price_interval G C w y sub
  dsimp only at a b
  have sBound : ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card ≤ 12 :=
    (Finset.card_le_card (fun i hi => (Finset.mem_inter.mp (Finset.mem_sdiff.mp hi).1).1)).trans sx
  have h := p _ _ _ a.1 a.2 b.1 b.2 sBound
  apply free13_of_chart_price G C sym irr link R41 sub coreNonlone x w y (Csym cwx) (Csym cwy)
    hxy xyne rx ry A (actual_center_witness G C w x y A sub vA) ia
  dsimp only
  omega

#print axioms actual_link_price_interval
#print axioms free13_of_local_chart
end Erdos151H13
