import HaarClass6OddNoThree

namespace HaarAbelianThirdOdd
open HaarClass4Ports HaarClass4Generate HaarUniversal36 HaarAllNoncommuting
open HaarClass5TemplateClosure HaarClass6ParallelWords HaarClass6ParallelCycle
open HaarClass6OddNoThree (v_swapped swap_cycle)
open HaarClass3Collector64 HaarHalfCollision
open scoped commutatorElement
variable {G : Type*} [Group G]

def AbelianThird (G : Type*) [Group G] : Prop :=
  ∀ a b : G, a∈L G 2 → b∈L G 2 → Commute a b

theorem close_abelian (h : AbelianThird G) (x y : G) : prodFrom x y 0 W=1 := by
  have b : prodFrom x y 0 B∈L G 2 := by
    apply tail_word x y B rowB zeroB
    · intro i hi
      rw [lenB] at hi
      exact stepsB ⟨i,hi⟩
    · rw [lenB,finalB]; decide
  have ab := h _ _ (tail_A x y) b
  rw [concat]
  simp only [prod_append,List.length_append,lenA,lenB,List.length_reverse]
  have eh : prodFrom x y (0+12) B=prodFrom x y 0 B :=
    prod_same_sign x y _ _ _ (by decide)
  rw [eh,prod_reverse x y (0+12+20) 0 A (by rw [lenA]),
    prod_reverse x y (0+12+20+12) 0 B (by rw [lenB])]
  exact ab.commutator_eq

theorem no_cube (nil : ∃ d, L G d=⊥) (deep : L G 2≠⊥) (n3 : ¬3∣Nat.card G)
    (x y : G) (gen : Generates x y) :
    let f := QuotientGroup.mk' (L G 3)
    ¬ ((portU (f x) (f y))^(3:ℕ)=1 ∧ (portV (f x) (f y))^(3:ℕ)=1) := by
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  change ¬ ((portU X Y)^(3:ℕ)=1 ∧ (portV X Y)^(3:ℕ)=1)
  rintro ⟨hu,hv⟩
  have nQ : ¬3∣Nat.card (G ⧸ S) := fun d => n3 (d.trans S.card_quotient_dvd_card)
  have eu := HaarClass5OddNoThree.cube_one nQ _ hu
  have ev := HaarClass5OddNoThree.cube_one nQ _ hv
  have cx : Commute (portC X Y) X := commutatorElement_eq_one_iff_commute.mp eu
  have cy : Commute (portC X Y) Y := commutatorElement_eq_one_iff_commute.mp ev
  have g : Generates X Y := map_gen f (QuotientGroup.mk'_surjective S) gen
  have bot : L (G ⧸ S) 2=⊥ := c_center_class_two X Y _ g (ports_xy X Y) (gen_center X Y _ g cx cy)
  have M : (L G 2).map f = L (G ⧸ S) 2 := map_ls f (QuotientGroup.mk'_surjective S) 2
  rw [bot,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at M
  have same : L G 2=L G 3 := le_antisymm M
    (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by decide : 2≤3))
  have all (n : ℕ) : L G (2+n)=L G 2 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change ⁅L G (2+n),(⊤ : Subgroup G)⁆=L G 2
        rw [ih]
        exact same.symm
  obtain ⟨n,hn⟩ := nil
  have b : L G (2+n) ≤ ⊥ :=
    (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (show n≤2+n by omega)).trans (le_of_eq hn)
  exact deep ((all n).symm.trans (le_bot_iff.mp b))

theorem generated (nil : ∃ d, L G d=⊥) (ab : AbelianThird G) (deep : L G 2≠⊥)
    (odd : Odd (Nat.card G)) (n3 : ¬3∣Nat.card G) (x y : G) (gen : Generates x y) :
    HasCycle x y 64 := by
  let f := QuotientGroup.mk' (L G 3)
  have nc := no_cube nil deep n3 x y gen
  by_cases nv : (portV (f x) (f y))^(3:ℕ)=1
  · apply swap_cycle
    apply case_v_with_close odd y x (close_abelian ab y x)
    change (portV (f y) (f x))^(3:ℕ)≠1
    simp only [v_swapped (quote_nil 3),inv_pow,ne_eq,inv_eq_one]
    exact fun u => nc ⟨u,nv⟩
  · exact case_v_with_close odd x y (close_abelian ab x y) nv

theorem normalized (nil : ∃ d, L G d=⊥) (ab : AbelianThird G)
    (odd : Odd (Nat.card G)) (n3 : ¬3∣Nat.card G)
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HasCycle x y (2^e) := by
  let S := Subgroup.closure ({x,y} : Set G)
  let X : S := ⟨x,Subgroup.subset_closure (by simp)⟩
  let Y : S := ⟨y,Subgroup.subset_closure (by simp)⟩
  have gen : Generates X Y := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure,Set.image_pair,Subgroup.map_top,Subgroup.subtype_range]
    rfl
  have mono (n : ℕ) : (L S n).map S.subtype ≤ L G n := by
    rw [Subgroup.top_subtype_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono n (show S≤⊤ from le_top)
  have cls : ∃ n, L S n=⊥ := by
    obtain ⟨n,hn⟩ := nil
    refine ⟨n,?_⟩
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_bot]
    exact le_bot_iff.mp ((mono n).trans (le_of_eq hn))
  have abS : AbelianThird S := by
    intro a b ha hb
    exact Subtype.ext (ab a.val b.val ((mono 2) (Subgroup.mem_map_of_mem S.subtype ha))
      ((mono 2) (Subgroup.mem_map_of_mem S.subtype hb))).eq
  have hxS : X≠1 := fun e => hx (congrArg Subtype.val e)
  have hyS : Y≠1 := fun e => hy (congrArg Subtype.val e)
  have hxyS : X≠Y := fun e => hxy (congrArg Subtype.val e)
  have oddS : Odd (Nat.card S) := Odd.of_dvd_nat odd S.card_subgroup_dvd_card
  have n3S : ¬3∣Nat.card S := fun e => n3 (e.trans S.card_subgroup_dvd_card)
  have lift (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    HaarClassFourFinite.mapped_cycle S.subtype Subtype.val_injective X Y
  by_cases c : L S 2=⊥
  · have c5 : L S 5=⊥ := le_bot_iff.mp
      ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup S) (by decide : 2≤5)).trans (le_of_eq c))
    obtain ⟨e,lo,hi,cy⟩ := HaarClass5Odd.normalized c5 oddS X Y hxS hyS hxyS
    exact ⟨e,lo,hi,lift _ cy⟩
  · exact ⟨6,by decide,by decide,lift 64 (generated cls abS c oddS n3S X Y gen)⟩

theorem any_ports (nil : ∃ d, L G d=⊥) (ab : AbelianThird G)
    (odd : Odd (Nat.card G)) (n3 : ¬3∣Nat.card G)
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HaarAnyPorts.HasPortCycle r s t (2^e) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,lo,hi,cy⟩ := normalized nil ab odd n3 (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,lo,hi,HaarAnyPorts.map_cycle r s t cy⟩

end HaarAbelianThirdOdd
#print axioms HaarAbelianThirdOdd.any_ports
