import H12EdgePolicies
import UpperIncidence
namespace Erdos151H12
open Erdős151 Erdős151.Upper
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) [DecidableRel G]
/-- Exact adjacent two-hub price bound using chosen independent exclusive pools.
The large-pool hypothesis may be supplied by the induced monotonicity of free sets
and an explicit order-50 hypothesis. Only ambient forbidden cliques occur here. -/
theorem adjacent_two_hub_price_h13
    (sym : ∀ {x y}, G x y → G y x) (irr : ∀ x, ¬ G x x)
    (u v : V) (huv : G u v) (notLone : ¬ Lone G u v)
    (A B : Finset V)
    (hA : ∀ a ∈ A, G u a ∧ ¬ G v a ∧ a ≠ v ∧ ¬ Lone G u a)
    (hB : ∀ b ∈ B, G v b ∧ ¬ G u b ∧ b ≠ u ∧ ¬ Lone G v b)
    (iA : Erdos151Ramsey.Independent G A) (iB : Erdos151Ramsey.Independent G B)
    (lower : ∀ R : Finset V, 50 ≤ R.card →
      ∃ P ⊆ R, 11 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (price : 50 + (neighbors G u).card + (neighbors G v).card ≤
       Fintype.card V + ((neighbors G u) ∩ (neighbors G v)).card + A.card + B.card) :
    ∃ P : Finset V, 13 ≤ P.card ∧ Free (Forbidden G) (P : Set V) := by
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
  have hr : 50 ≤ R.card := by omega
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


variable (C : V → V → Prop) [DecidableRel C]
theorem adjacent_core_necessary_h13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (symC : ∀ {a b}, C a b → C b a) (tf : TriangleFreeLinks G)
    (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C)
    (lower : ∀ R : Finset V, 50 ≤ R.card →
      ∃ P ⊆ R, 11 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12)
    (u v : V) (huv : C u v) :
    Fintype.card V + twoHubFloor (neighbors C u).card (neighbors C v).card (ambientCodeg G u v)
      ≤ 49 + (neighbors G u).card + (neighbors G v).card := by
  have heq : ambientCodeg G u v = ambientCodeg G v u := by
    simp [ambientCodeg, Finset.inter_comm]
  obtain ⟨A,hA,hAc,hAi⟩ := eligible_independent (G := G) (C := C) sym irr tf mono t u v huv
  obtain ⟨B,hB,hBc,hBi⟩ := eligible_independent (G := G) (C := C) sym irr tf mono t v u (symC (a := u) (b := v) huv)
  rw [←heq] at hBc
  have notLone : ¬ Lone G u v := by
    obtain ⟨x,_,_,hux,hvx,_,_⟩ := t u v huv
    exact fun h => h.2 x ⟨mono hux,mono hvx⟩
  by_contra! hbad
  unfold twoHubFloor at hbad
  have pw : 50 + (neighbors G u).card + (neighbors G v).card ≤
       Fintype.card V + ((neighbors G u) ∩ (neighbors G v)).card + A.card + B.card := by
    unfold ambientCodeg at hbad hAc hBc
    omega
  obtain ⟨P,hp,hf⟩ := adjacent_two_hub_price_h13 G sym irr u v (mono huv) notLone A B
    (fun x hx => (mem_eligible G).mp (hA hx))
    (fun x hx => (mem_eligible G).mp (hB hx))
    hAi hBi lower pw
  have := upper P hf
  omega

theorem low_ambient_rows_at_least64_h13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (symC : ∀ {a b}, C a b → C b a) (tf : TriangleFreeLinks G)
    (mono : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (degree : ∀ v, (neighbors G v).card ≤ 12)
    (lower : ∀ R : Finset V, 50 ≤ R.card →
      ∃ P ⊆ R, 11 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12)
    (hn : 64 ≤ Fintype.card V)
    (w : V) (hd : (neighbors G w).card ≤ 10)
    (hr : 10 ≤ (neighbors C w).card)
    (cmin : ∀ u∈neighbors C w, 8 ≤ (neighbors C u).card) :
    (∑ u∈neighbors C w,row C (neighbors C w) u) = 2*(neighbors C w).card := by
  have book (u : V) (hu : u ∈ neighbors C w) : row C (neighbors C w) u = 2 := by
    have hwu := (mem_neighbors C).mp hu
    have hnec := adjacent_core_necessary_h13 G C sym irr symC tf mono two lower upper w u hwu
    have hu12 := degree u
    have hlim : twoHubFloor (neighbors C w).card (neighbors C u).card (ambientCodeg G w u) ≤ 7 := by omega
    have hlo := core_overlap_has_two G C mono two w u hwu
    have hloC := core_overlap_has_two C C (fun h => h) two w u hwu
    have hmono := core_book_le_ambient G C mono w u
    have hh := twoHubFloor_le_seven _ _ _ (by omega) (cmin u hu) hlo hlim
    have hc : ambientCodeg C w u = 2 := by
      rcases hh with h|h|h <;> omega
    have he : row C (neighbors C w) u = ambientCodeg C w u := by
      unfold row ambientCodeg
      congr 1
      ext x
      simp [mem_neighbors]
    exact he.trans hc
  rw [Finset.sum_congr rfl book]
  simp [Nat.mul_comm]

#print axioms adjacent_core_necessary_h13
#print axioms low_ambient_rows_at_least64_h13
end Erdos151H12
