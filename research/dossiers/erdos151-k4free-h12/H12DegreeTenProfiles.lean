import H12DegreeTenCounts
import H12OwnerExtremes
import H12StarSelection

namespace Erdos151H12
open Erdős151 Erdos151Ramsey
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G : V → V → Prop)

noncomputable def singlesFor (S B : Finset V) (u : V) : Finset V :=
  weightedSet (weightedSet B (Acol G S)) (fun x => u ∈ ns (G:=G) S x)

theorem mem_singlesFor {S B : Finset V} {u x : V} :
    x ∈ singlesFor G S B u ↔ x∈B ∧ Acol G S x ∧ u ∈ ns (G:=G) S x := by
  classical
  simp [singlesFor,weightedSet,and_assoc]

theorem singlesFor_sum (S B : Finset V) :
    ∑ u∈S,(singlesFor G S B u).card = (weightedSet B (Acol G S)).card := by
  classical
  let A := weightedSet B (Acol G S)
  let R (u x : V) : Prop := u ∈ ns (G:=G) S x
  have co (x : V) : colCount S R x = (ns (G:=G) S x).card := by
    unfold colCount
    congr 1
    ext w
    simp only [Finset.mem_filter,R]
    exact ⟨And.right,fun H => ⟨((mem_ns (G:=G) S x).mp H).1,H⟩⟩
  have row (u : V) : rowCount A R u = (singlesFor G S B u).card := by
    unfold rowCount singlesFor
    congr 1
    ext x
    simp [A,R,weightedSet]
  have hf := flipCounts S A R
  simp only [co,row] at hf
  rw [←hf]
  calc
    _ = ∑ _x∈A,(1:Nat) := Finset.sum_congr rfl (by
      intro x hx
      exact (Finset.mem_filter.mp hx).2)
    _ = _ := by simp [A]

theorem singlesFor_ownership
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S B : Finset V) (hS : Free (Forbidden G) (S : Set V))
    (blocked : ∀ x∈B, ¬ Free (Forbidden G) (insert x (S : Set V)))
    (u x : V) (hx : x ∈ singlesFor G S B u) :
    Lone G u x ∧ (∀ y∈S, G x y→y=u) ∧ x∈lonePrivatePool G S B u := by
  obtain ⟨hxB,ha,hu⟩ := (mem_singlesFor G).mp hx
  have hOne : (ns (G:=G) S x).card = 1 := ha
  have hLs := (blocked_one_lone (G:=G) S x sym irr hS (blocked x hxB) hOne).1
  have heq := Finset.eq_of_subset_of_card_le (lone_support_subset (G:=G) S x)
    (show (ns (G:=G) S x).card ≤ (ls (G:=G) S x).card by omega)
  have huL : u ∈ ls (G:=G) S x := heq ▸ hu
  have hL := ((mem_ls (G:=G) S x).mp huL).2
  have hOnly (y : V) (hy : y∈ ns (G:=G) S x) : y = u := by
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hOne
    exact (by simpa [hv] using hy : y=v).trans (by simpa [hv] using hu : u=v).symm
  have hP := owner_of_small_support (G:=G) S x sym irr hS hu (by omega)
    (fun a ha => hOnly a (lone_support_subset (G:=G) S x ha))
  exact ⟨lone_symm G sym hL,
    fun y hy hg => hOnly y ((mem_ns (G:=G) S x).mpr ⟨hy,hg⟩),
    (mem_lonePrivatePool G).mpr ⟨hxB,(mem_qs (G:=G) S x).mpr
      ⟨((mem_ls (G:=G) S x).mp huL).1,hL,((mem_ps (G:=G) S x).mp hP).2⟩⟩⟩

theorem singlesFor_cap
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S B : Finset V) (h10 : S.card=10) (hS : Free (Forbidden G) (S : Set V))
    (hBS : Disjoint B S)
    (blocked : ∀ x∈B, ¬ Free (Forbidden G) (insert x (S : Set V)))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (u : V) (hu : u∈S) :
    (singlesFor G S B u).card ≤ 2 ∧
      (∀ x∈privatePool G S B u, x∉singlesFor G S B u → (singlesFor G S B u).card ≤ 1) := by
  have hIso := privatePool_isolated G sym S B hS hBS blocked u
  have hAlpha := privatePool_alpha_two G sym S B h10 hS hBS upper u hu
  have core : IsolatedIn G (singlesFor G S B u) (privatePool G S B u) := by
    have hsub : singlesFor G S B u ⊆ lonePrivatePool G S B u :=
      fun x hx => (singlesFor_ownership G sym irr S B hS blocked u x hx).2.2
    exact ⟨hsub.trans hIso.1,fun a ha b hb => hIso.2 a (hsub ha) b hb⟩
  refine ⟨hAlpha _ core.1 (fun x hx y hy => core.2 x hx y (core.1 hy)), ?_⟩
  intro x hx hxn
  have hs : ({x} : Finset V) ⊆ privatePool G S B u \ singlesFor G S B u :=
    Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨hx,hxn⟩)
  have hi : Independent G ({x} : Finset V) := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    simpa [ha,hb] using irr x
  have hsum := add_of_isolated_le G sym core hs hi hAlpha
  simp only [Finset.card_singleton] at hsum
  omega

theorem degreeTen_nineteen_impossible
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S B : Finset V) (h10 : S.card=10) (hS : Free (Forbidden G) (S : Set V))
    (hBS : Disjoint B S)
    (blocked : ∀ x∈B, ¬ Free (Forbidden G) (insert x (S : Set V)))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (h19 : 19 ≤ (weightedSet B (Acol G S)).card)
    (hB : (weightedSet B (Bcol G S)).Nonempty) : False := by
  classical
  obtain ⟨x,hx⟩ := hB
  have ⟨hxB,hxCase⟩ := Finset.mem_filter.mp hx
  have ⟨hn,hl⟩ := hxCase
  have hl0 : (ls (G:=G) S x).card = 0 := hl
  obtain ⟨u,v,huv,hEq⟩ := Finset.card_eq_two.mp hn
  have hu : u∈ns (G:=G) S x := by simp [hEq]
  have hv : v∈ns (G:=G) S x := by simp [hEq]
  have frame (w : V) (hw : w∈ns (G:=G) S x) :
      w∈S ∧ (singlesFor G S B w).card ≤ 1 := by
    have hS' := ((mem_ns (G:=G) S x).mp hw).1
    have hp := owner_of_small_support (G:=G) S x sym irr hS hw (by exact hn.le)
      (fun a ha => False.elim (by
        have hpos := Finset.card_pos.mpr (show (ls (G:=G) S x).Nonempty from ⟨a,ha⟩)
        omega))
    have hxP := (mem_privatePool G).mpr ⟨hxB,hp⟩
    have hnS : x ∉ singlesFor G S B w := by
      intro h
      have hn' : ncol G S x = 1 := ((mem_singlesFor G).mp h).2.1
      omega
    exact ⟨hS',(singlesFor_cap G sym irr S B h10 hS hBS blocked upper w hS').2 x hxP hnS⟩
  have ⟨huS,hul⟩ := frame u hu
  have ⟨hvS,hvl⟩ := frame v hv
  apply nineteen_not_two_available S (fun w => (singlesFor G S B w).card) h10
    (fun w hw => (singlesFor_cap G sym irr S B h10 hS hBS blocked upper w hw).1)
    (by rw [singlesFor_sum G S B]; exact h19) u v huS hvS huv hul hvl

theorem degreeTen_twenty_impossible [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S B : Finset V) (h10 : S.card=10) (hS : Free (Forbidden G) (S : Set V))
    (hBS : Disjoint B S)
    (blocked : ∀ x∈B, ¬ Free (Forbidden G) (insert x (S : Set V)))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (degree : ∀ v, (neighbors G v).card ≤ 11)
    (u v : V) (hu : u∉S) (hv : v∉S) (hUV : Lone G u v)
    (noUV : ∀ s∈S, ¬G u s ∧ ¬G v s)
    (h20 : 20 ≤ (weightedSet B (Acol G S)).card)
    (hD : (weightedSet B (Dcol G S)).Nonempty) : False := by
  classical
  obtain ⟨d,hd⟩ := hD
  have ⟨hdB,hdCase⟩ := Finset.mem_filter.mp hd
  have hn : (ns (G:=G) S d).card = 2 := hdCase.1
  have hl : (ls (G:=G) S d).card = 2 := hdCase.2
  have hAll := Finset.eq_of_subset_of_card_le (lone_support_subset (G:=G) S d)
    (show (ns (G:=G) S d).card ≤ (ls (G:=G) S d).card by omega)
  obtain ⟨s,t,hst,hEq⟩ := Finset.card_eq_two.mp hl
  have hs : s∈ls (G:=G) S d := by simp [hEq]
  have ht : t∈ls (G:=G) S d := by simp [hEq]
  have hSD := (mem_ls (G:=G) S d).mp hs
  have hTD := (mem_ls (G:=G) S d).mp ht
  have part (w : V) (hw : w∈S) : ∃ a b, a≠b ∧ singlesFor G S B w = {a,b} := by
    have he := twenty_every_owner_two S (fun w => (singlesFor G S B w).card) h10
      (fun w hw => (singlesFor_cap G sym irr S B h10 hS hBS blocked upper w hw).1)
      (by rw [singlesFor_sum G S B]; exact h20) w hw
    exact Finset.card_eq_two.mp he
  let part₀ (w : V) (hw : w∈S) := Classical.choose (part w hw)
  let part₁ (w : V) (hw : w∈S) := Classical.choose (Classical.choose_spec (part w hw))
  have hPair (w : V) (hw : w∈S) :
      part₀ w hw ≠ part₁ w hw ∧ singlesFor G S B w = {part₀ w hw,part₁ w hw} :=
    Classical.choose_spec (Classical.choose_spec (part w hw))
  let L (w : V) (b : Bool) : V := if hw:w∈S then if b then part₁ w hw else part₀ w hw else d
  have hmem (w : V) (hw : w∈S) (b : Bool) : L w b ∈ singlesFor G S B w := by
    rw [(hPair w hw).2]
    cases b <;> simp [L,hw]
  have hds : ∀ x∈S, G d x → x=s ∨ x=t := by
    intro x hx hdX
    have hxL : x ∈ ls (G:=G) S d := by
      rw [hAll]
      exact (mem_ns (G:=G) S d).mpr ⟨hx,hdX⟩
    simpa [hEq] using hxL
  refine twenty_singletons_exchange G sym irr upper degree S h10 hS u v d s t hu hv
    (Finset.disjoint_left.mp hBS hdB) hUV noUV hSD.1 hTD.1 hst
    (lone_symm G sym hSD.2) (lone_symm G sym hTD.2) hds L ?_ ?_
  · intro w hw b
    have h := hmem w hw b
    have ho := singlesFor_ownership G sym irr S B hS blocked w (L w b) h
    exact ⟨Finset.disjoint_left.mp hBS ((mem_singlesFor G).mp h).1,ho.1,ho.2.1⟩
  · intro w hw
    simpa [L,hw] using (hPair w hw).1

#print axioms singlesFor_sum
#print axioms degreeTen_nineteen_impossible
#print axioms degreeTen_twenty_impossible
end Erdos151H12
