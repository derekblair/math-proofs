import N63ActualLink

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey

private theorem exact_medium_chart : ∀ i j : Fin 4, ∀ k : Fin 13,
    (i.val+3)+(j.val+3)+k.val+2+outerFloor (i.val+3) (j.val+3) k.val ≤ 12 →
    i.val=0 ∧ j.val=0 ∧ k.val=0 := by decide

private theorem scalar_failing_medium_pair (a b s : ℕ)
    (aL : 3 ≤ a) (aU : a ≤ 6) (bL : 3 ≤ b) (bU : b ≤ 6) (sU : s ≤ 12)
    (p : a+b+s+2+outerFloor a b s ≤ 12) :
    a=3 ∧ b=3 ∧ s=0 := by
  let i : Fin 4 := ⟨a-3, by omega⟩
  let j : Fin 4 := ⟨b-3, by omega⟩
  let k : Fin 13 := ⟨s, by omega⟩
  have ai : i.val+3=a := by change a-3+3=a; omega
  have bj : j.val+3=b := by change b-3+3=b; omega
  have h := exact_medium_chart i j k (by simpa only [ai,bj] using p)
  change a-3=0 ∧ b-3=0 ∧ s=0 at h
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem failed_medium_pair_unique_prices
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (Csym : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (cwx : C w x) (cwy : C w y) (hxy : ¬ G x y) (xyne : x ≠ y)
    (rx : 8 ≤ (neighbors C x).card) (ry : 8 ≤ (neighbors C y).card)
    (rw : (neighbors C w).card=9) (n : 63 ≤ Fintype.card V)
    (dx : (neighbors G x).card ≤ 12) (dy : (neighbors G y).card ≤ 12) (dw : (neighbors G w).card ≤ 12)
    (px : actualLinkDegree G C w x = 3) (py : actualLinkDegree G C w y = 3)
    (A : Finset V) (vA : ∀ v ∈ A, C w v ∧ v ≠ x ∧ v ≠ y ∧ ¬ G x v ∧ ¬ G y v)
    (ia : Independent G A) (ac : 2 ≤ A.card)
    (no : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V)) :
    (neighbors G x∩neighbors G w).card=3 ∧
    (neighbors G y∩neighbors G w).card=3 ∧
    ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card=0 ∧
    (neighbors G x).card=12 ∧ (neighbors G y).card=12 ∧ (neighbors G w).card=12 := by
  let a := (neighbors G x∩neighbors G w).card
  let b := (neighbors G y∩neighbors G w).card
  let s := ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
  have aI : 3 ≤ a ∧ a ≤ 6 := by
    have h := actual_link_price_interval G C w x sub
    change actualLinkDegree G C w x ≤ a ∧ _ at h
    omega
  have bI : 3 ≤ b ∧ b ≤ 6 := by
    have h := actual_link_price_interval G C w y sub
    change actualLinkDegree G C w y ≤ b ∧ _ at h
    omega
  have sU : s ≤ 12 :=
    (Finset.card_le_card (fun i hi => (Finset.mem_inter.mp (Finset.mem_sdiff.mp hi).1).1)).trans dx
  have p : ¬ ((neighbors G x).card + (neighbors G y).card + (neighbors G w).card + 40 ≤
      Fintype.card V + a + b + s + A.card + outerFloor a b s) := by
    intro p
    exact no (free13_of_chart_price G C sym irr link R41 sub coreNonlone x w y
      (Csym cwx) (Csym cwy) hxy xyne rx ry A (actual_center_witness G C w x y A sub vA) ia p)
  obtain ⟨ha,hb,hs⟩ := scalar_failing_medium_pair a b s aI.1 aI.2 bI.1 bI.2 sU (by omega)
  have ofloor : outerFloor a b s = 4 := by
    rw [ha,hb,hs]
    decide
  exact ⟨ha,hb,hs,by omega,by omega,by omega⟩

/-- When the actual book size agrees with the induced chart, no extra
ambient vertex of the center can attach to this pivot. -/
theorem no_new_center_attachments (w x z : V)
    (sub : ∀ a b, C a b → G a b)
    (price : (neighbors G x∩neighbors G w).card = actualLinkDegree G C w x)
    (wz : G w z) (nc : ¬ C w z) : ¬ G x z := by
  let A := neighbors G x∩neighbors G w
  let B := neighbors G x∩neighbors C w
  have bA : B ⊆ A := by
    intro u hu
    obtain ⟨hx,hw⟩ := Finset.mem_inter.mp hu
    exact Finset.mem_inter.mpr ⟨hx,(mem_neighbors G).mpr (sub w u ((mem_neighbors C).mp hw))⟩
  change A.card=B.card at price
  have eq : B=A := Finset.eq_of_subset_of_card_le bA price.le
  intro xz
  have m : z ∈ A := Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr xz,(mem_neighbors G).mpr wz⟩
  rw [←eq] at m
  exact nc ((mem_neighbors C).mp (Finset.mem_inter.mp m).2)

/-- No pair of marked medium neighbors can share a vertex outside the
center and its ambient link if its exterior overlap price is zero. -/
theorem no_shared_exterior (w x y z : V)
    (price : ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card=0)
    (nzw : z ≠ w) (nwz : ¬ G w z) (xz : G x z) : ¬ G y z := by
  intro yz
  have m : z ∈ (neighbors G x∩neighbors G y)\insert w (neighbors G w) := by
    simp [mem_neighbors,nzw,nwz,xz,yz]
  rw [Finset.card_eq_zero.mp price] at m
  exact Finset.notMem_empty _ m

#print axioms failed_medium_pair_unique_prices
#print axioms no_new_center_attachments
#print axioms no_shared_exterior
end Erdos151H13
