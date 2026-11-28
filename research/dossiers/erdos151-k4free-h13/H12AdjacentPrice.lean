import H12PairInsert

namespace Erdos151H12
open Erdős151

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) [DecidableRel G]

def neighbors (u : V) : Finset V := Finset.univ.filter (G u)

theorem mem_neighbors {u x : V} : x ∈ neighbors G u ↔ G u x := by
  simp [neighbors]

/-- Exact adjacent two-hub price bound using chosen independent exclusive pools.
The large-pool hypothesis may be supplied by the induced monotonicity of free sets
and the universal order-41 result. Only ambient forbidden cliques occur here. -/
theorem adjacent_two_hub_price
    (sym : ∀ {x y}, G x y → G y x) (irr : ∀ x, ¬ G x x)
    (u v : V) (huv : G u v) (notLone : ¬ Lone G u v)
    (A B : Finset V)
    (hA : ∀ a ∈ A, G u a ∧ ¬ G v a ∧ a ≠ v ∧ ¬ Lone G u a)
    (hB : ∀ b ∈ B, G v b ∧ ¬ G u b ∧ b ≠ u ∧ ¬ Lone G v b)
    (iA : Erdos151Ramsey.Independent G A) (iB : Erdos151Ramsey.Independent G B)
    (lower : ∀ R : Finset V, 41 ≤ R.card →
      ∃ P ⊆ R, 10 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (price : 41 + (neighbors G u).card + (neighbors G v).card ≤
       Fintype.card V + ((neighbors G u) ∩ (neighbors G v)).card + A.card + B.card) :
    ∃ P : Finset V, 12 ≤ P.card ∧ Free (Forbidden G) (P : Set V) := by
  let U := (neighbors G u).erase v
  let W := (neighbors G v).erase u
  let D := (U ∪ W) \ (A ∪ B)
  let Base := ((Finset.univ : Finset V).erase u).erase v
  let R := Base \ D
  have hn : u ≠ v := fun e => irr u (e ▸ huv)
  have huU : u ∉ U := fun h => irr u (mem_neighbors G |>.mp (Finset.mem_erase.mp h).2)
  have hvW : v ∉ W := fun h => irr v (mem_neighbors G |>.mp (Finset.mem_erase.mp h).2)
  have huW : u ∉ W := Finset.notMem_erase _ _
  have hvU : v ∉ U := Finset.notMem_erase _ _
  have hUa : A ⊆ U := fun a ha =>
    Finset.mem_erase.mpr ⟨(hA a ha).2.2.1, (mem_neighbors G).mpr (hA a ha).1⟩
  have hWb : B ⊆ W := fun b hb =>
    Finset.mem_erase.mpr ⟨(hB b hb).2.2.1, (mem_neighbors G).mpr (hB b hb).1⟩
  have hAB : (A ∪ B) ⊆ (U ∪ W) :=
    Finset.union_subset (fun x hx => Finset.mem_union_left _ (hUa hx))
      (fun x hx => Finset.mem_union_right _ (hWb hx))
  have hABd : Disjoint A B := Finset.disjoint_left.mpr
    (fun x xa xb => (hA x xa).2.1 (hB x xb).1)
  have hDU : D ⊆ Base := by
    intro x hx
    have he := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp he.1 with hh | hh
    · exact Finset.mem_erase.mpr ⟨fun eq => hvU (eq ▸ hh),Finset.mem_erase.mpr
        ⟨fun eq => huU (eq ▸ hh), Finset.mem_univ _⟩⟩
    · exact Finset.mem_erase.mpr ⟨fun eq => hvW (eq ▸ hh),Finset.mem_erase.mpr
        ⟨fun eq => huW (eq ▸ hh), Finset.mem_univ _⟩⟩
  have hUW : U ∩ W = neighbors G u ∩ neighbors G v := by
    ext x
    simp only [U, W, Finset.mem_inter, Finset.mem_erase]
    constructor
    · exact fun ⟨hx,hy⟩ => ⟨hx.2,hy.2⟩
    · intro ⟨ha,hb⟩
      refine ⟨⟨?_,ha⟩,⟨?_,hb⟩⟩
      · rintro rfl
        exact irr _ ((mem_neighbors G).mp hb)
      · rintro rfl
        exact irr _ ((mem_neighbors G).mp ha)
  have hU := Finset.card_erase_add_one ((mem_neighbors G).mpr huv)
  have hW := Finset.card_erase_add_one ((mem_neighbors G).mpr (sym huv))
  have hbase : Base.card + 2 = Fintype.card V := by
    have h1 := Finset.card_erase_add_one (Finset.mem_univ u)
    have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr
      ⟨hn.symm, Finset.mem_univ v⟩)
    change Base.card+1 = _ at h2
    simp only [Finset.card_univ] at h1
    omega
  have ho := Finset.card_union_add_card_inter U W
  rw [hUW] at ho
  have hD := Finset.card_sdiff_add_card_eq_card hAB
  have hR := Finset.card_sdiff_add_card_eq_card hDU
  rw [Finset.card_union_of_disjoint hABd] at hD
  change D.card + (A.card+B.card) = (U ∪ W).card at hD
  change R.card + D.card = Base.card at hR
  change U.card+1 = _ at hU
  change W.card+1 = _ at hW
  have hr : 41 ≤ R.card := by omega
  obtain ⟨P,hP,hPc,hFree⟩ := lower R hr
  have hbaseP (x : V) (hx : x ∈ P) : x ∈ Base := (Finset.mem_sdiff.mp (hP hx)).1
  have huP : u ∉ P := fun hm => (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hbaseP u hm))).1 rfl
  have hvP : v ∉ P := fun hm => (Finset.mem_erase.mp (hbaseP v hm)).1 rfl
  have huA (x : V) (hx : x ∈ P) (hu : G u x) : x ∈ A := by
    have hmem : x ∈ U := Finset.mem_erase.mpr ⟨fun e => hvP (e ▸ hx), (mem_neighbors G).mpr hu⟩
    have hnD := (Finset.mem_sdiff.mp (hP hx)).2
    by_contra hna
    have hnb : x ∉ B := fun hxb => (hB x hxb).2.1 hu
    apply hnD
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hmem,
      fun he => (Finset.mem_union.mp he).elim hna hnb⟩
  have hvB (x : V) (hx : x ∈ P) (hv : G v x) : x ∈ B := by
    have hmem : x ∈ W := Finset.mem_erase.mpr ⟨fun e => huP (e ▸ hx), (mem_neighbors G).mpr hv⟩
    have hnD := (Finset.mem_sdiff.mp (hP hx)).2
    by_contra hnb
    have hna : x ∉ A := fun hxa => (hA x hxa).2.1 hv
    apply hnD
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hmem,
      fun he => (Finset.mem_union.mp he).elim hna hnb⟩
  have hsafe : Free (Forbidden G) (insert u (insert v (P : Set V))) := by
    apply safe_insert_two G sym irr _ u v hFree notLone
    · exact fun x hx => ⟨fun hl => (hA x (huA x hx hl.1)).2.2.2 hl,
        fun hl => (hB x (hvB x hx hl.1)).2.2.2 hl⟩
    · intro z hz x hx y hy hzx hzy
      rcases hz with rfl|rfl
      · exact iA x (huA x hx hzx) y (huA y hy hzy)
      · exact iB x (hvB x hx hzx) y (hvB y hy hzy)
    · intro x hx _ hg
      exact (hA x (huA x hx hg)).2.1
  refine ⟨insert u (insert v P), ?_, by simpa only [Finset.coe_insert] using hsafe⟩
  have hno : u ∉ insert v P := by simp [hn,huP]
  rw [Finset.card_insert_of_notMem hno, Finset.card_insert_of_notMem hvP]
  omega

#print axioms adjacent_two_hub_price
end Erdos151H12
