import H12SaturatedStar
import H12AdjacentPrice

namespace Erdos151H12
open Erdős151

variable {V : Type*} [DecidableEq V] (G : V → V → Prop)

theorem forces_lone_by_two_leaves
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (S : Finset V) (hf : Free (Forbidden G) (S : Set V)) (h10 : S.card = 10)
    (s u a b : V) (hs : s ∈ S) (hu : u ∉ S) (ha : a ∉ S) (hb : b ∉ S)
    (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (hsa : Lone G s a) (hsb : Lone G s b)
    (hU : ∀ x ∈ S, ¬ G u x)
    (has : ∀ x ∈ S, G a x → x = s) (hbs : ∀ x ∈ S, G b x → x = s) :
    Lone G u a ∨ Lone G u b := by
  classical
  by_contra! h
  let S' := S.erase s
  let P : Finset V := {a,b} ∪ S'
  have hS : Free (Forbidden G) (S' : Set V) :=
    fun X hX hss => hf X hX (fun z hz => Finset.mem_of_mem_erase (hss hz))
  have hab' : ¬ G a b := fun e => hsa.2 b ⟨hsb.1,e⟩
  have hP : Free (Forbidden G) (P : Set V) := by
    apply free_adjoin_independent G sym irr _ _ hS
    · intro x hx y hy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
      rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
      · exact irr _
      · exact hab'
      · exact fun e => hab' (sym e)
      · exact irr _
    · intro x hx y hy hxy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      have ⟨hys,hyS⟩ := Finset.mem_erase.mp hy
      rcases hx with rfl|rfl
      · exact hys (has y hyS hxy)
      · exact hys (hbs y hyS hxy)
  have hPc : P.card = 11 := by
    have hdis : Disjoint ({a,b} : Finset V) S' := Finset.disjoint_left.mpr (by
      intro x hx hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact ha (Finset.mem_of_mem_erase hh)
      · exact hb (Finset.mem_of_mem_erase hh))
    have hS' := Finset.card_erase_add_one hs
    change S'.card+1 = S.card at hS'
    change (({a,b} : Finset V) ∪ S').card = 11
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hab),
      Finset.card_singleton]
    omega
  have huP : u ∉ P := by
    change u ∉ (({a,b} : Finset V) ∪ S')
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    exact fun hh => hh.elim (fun hh => hh.elim hua hub) (fun hs => hu (Finset.mem_of_mem_erase hs))
  have hN (x : V) (hx : x ∈ P) (hg : G u x) : x = a ∨ x = b := by
    change x ∈ (({a,b} : Finset V) ∪ S') at hx
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hx
    exact hx.resolve_right (fun hh => hU x (Finset.mem_of_mem_erase hh) hg)
  have hFree : Free (Forbidden G) (insert u (P : Set V)) := by
    apply safe_insert_one G sym irr _ u hP
    · intro x hx hL
      rcases hN x hx hL.1 with rfl|rfl
      · exact h.1 hL
      · exact h.2 hL
    · intro x hx y hy hux huy
      have hx' := hN x hx hux
      have hy' := hN y hy huy
      rcases hx' with rfl|rfl <;> rcases hy' with rfl|rfl
      · exact irr _
      · exact hab'
      · exact fun e => hab' (sym e)
      · exact irr _
  have hCap := upper (insert u P) (by simpa only [Finset.coe_insert] using hFree)
  rw [Finset.card_insert_of_notMem huP,hPc] at hCap
  omega

/-- The all-twenty-singletons profile plus one double-lone column is impossible.
No coloring, classification or Folkman-number lower bound is needed. -/
theorem twenty_singletons_exchange [Fintype V] [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (degree : ∀ v, (neighbors G v).card ≤ 11)
    (S : Finset V) (h10 : S.card = 10) (hf : Free (Forbidden G) (S : Set V))
    (u v d s t : V) (hu : u ∉ S) (hv : v ∉ S) (hd : d ∉ S)
    (huv : Lone G u v) (hUV : ∀ x ∈ S, ¬ G u x ∧ ¬ G v x)
    (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hsd : Lone G s d) (htd : Lone G t d)
    (hDS : ∀ x ∈ S, G d x → x = s ∨ x = t)
    (L : V → Bool → V)
    (hL : ∀ x ∈ S, ∀ b, L x b ∉ S ∧ Lone G x (L x b) ∧
      ∀ y ∈ S, G (L x b) y → y = x)
    (hTwo : ∀ x ∈ S, L x false ≠ L x true) : False := by
  classical
  have hPick (w : V) (hw : w ∉ S) (hwS : ∀ x ∈ S, ¬ G w x)
      (x : {x // x ∈ S}) : ∃ b : Bool, Lone G w (L x.val b) := by
    have ne (b : Bool) : w ≠ L x.val b := by
      intro eq
      exact hwS x.val x.property (eq.symm ▸ sym (hL x.val x.property b).2.1.1)
    rcases forces_lone_by_two_leaves G sym irr upper S hf h10 x.val w (L x.val false)
      (L x.val true) x.property hw (hL _ x.property false).1 (hL _ x.property true).1
      (ne false) (ne true) (hTwo _ x.property)
      (hL _ x.property false).2.1 (hL _ x.property true).2.1 hwS
      (hL _ x.property false).2.2 (hL _ x.property true).2.2 with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  let bv := fun x : {x // x ∈ S} => Classical.choose (hPick v hv (fun x hx => (hUV x hx).2) x)
  let lv := fun x : {x // x ∈ S} => L x.val (bv x)
  have hvl (x : {x // x ∈ S}) : Lone G v (lv x) :=
    Classical.choose_spec (hPick v hv (fun x hx => (hUV x hx).2) x)
  have own_inj {x y : V} (hx : x ∈ S) (hy : y ∈ S) {a b : Bool} (e : L x a = L y b) :
      x = y :=
    (hL y hy b).2.2 x hx (e ▸ sym (hL x hx a).2.1.1)
  let emb : {x // x ∈ S} ↪ V := ⟨lv,fun x y e => Subtype.ext (own_inj x.property y.property e)⟩
  let Y := S.attach.map emb
  have huY : u ∉ Y := by
    intro h
    obtain ⟨x,_,hx⟩ := Finset.mem_map.mp h
    change lv x = u at hx
    exact (hUV x.val x.property).1 (hx ▸ sym (hL x.val x.property (bv x)).2.1.1)
  have hc : (insert u Y).card = 11 := by
    rw [Finset.card_insert_of_notMem huY]
    change (S.attach.map emb).card + 1 = 11
    simp [h10]
  have hsat (x : V) (hx : x ∉ insert u Y) : ¬ G v x := by
    apply saturated_hub_neighbors G v (insert u Y) _ (by rw [hc]; exact degree v) x hx
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | hm
    · exact sym huv.1
    · obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hm
      exact (hvl q).1
  have hdL (x : V) (hx : x ∈ S) (b : Bool) : d ≠ L x b := by
    intro e
    have hs' := (hL x hx b).2.2 s hs (e ▸ sym hsd.1)
    have ht' := (hL x hx b).2.2 t ht (e ▸ sym htd.1)
    exact hst (hs'.trans ht'.symm)
  have hud : u ≠ d := fun e => (hUV s hs).1 (e.symm ▸ sym hsd.1)
  have hvd : v ≠ d := fun e => (hUV s hs).2 (e.symm ▸ sym hsd.1)
  have hvD : ¬ G v d := hsat d (by
    intro h
    rcases Finset.mem_insert.mp h with he|hm
    · exact hud he.symm
    · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hm
      exact hdL q.val q.property (bv q) he.symm)
  obtain ⟨bs,hus⟩ := hPick u hu (fun x hx => (hUV x hx).1) ⟨s,hs⟩
  obtain ⟨bt,hut⟩ := hPick u hu (fun x hx => (hUV x hx).1) ⟨t,ht⟩
  let a := L s bs
  let b := L t bt
  have hvna : ¬ G v a := fun h => huv.2 a ⟨hus.1,h⟩
  have hvnb : ¬ G v b := fun h => huv.2 b ⟨hut.1,h⟩
  have hvA : v ≠ a := fun e => (hUV s hs).2 (e.symm ▸ sym (hL s hs bs).2.1.1)
  have hvB : v ≠ b := fun e => (hUV t ht).2 (e.symm ▸ sym (hL t ht bt).2.1.1)
  obtain ⟨P,hcP,hFree⟩ := same_layer_exchange G sym irr S hf h10 s t u v d a b hs ht hst
    hv hd (hL s hs bs).1 (hL t ht bt).1 hvd hvA hvB (hdL s hs bs) (hdL t ht bt)
    (fun e => hst (own_inj hs ht e)) (fun x hx => (hUV x hx).2) hvD hvna hvnb
    hsd htd (hL s hs bs).2.1 (hL t ht bt).2.1 hus hut hDS (hL s hs bs).2.2 (hL t ht bt).2.2
  have := upper P hFree
  omega

#print axioms forces_lone_by_two_leaves
#print axioms twenty_singletons_exchange
end Erdos151H12
