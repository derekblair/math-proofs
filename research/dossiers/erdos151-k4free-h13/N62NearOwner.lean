import N62ChargeSaturation
import N62DoubledBExchange
import N62GhostInactivity

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

structure NearOwnerFrame (S X : Finset V) where
  marks : Finset V
  doubles : Finset V
  leaf : V→V
  markSub : marks⊆S
  leafData : ∀ u∈marks, leaf u∈X ∧ Lone G u (leaf u) ∧ supported G S {u} (leaf u)
  dblData : ∀ z∈doubles, z∈X ∧ ∃ a∈S, ∃ b∈S, a≠b ∧
    Lone G a z ∧ Lone G b z ∧ support G S z={a,b}

noncomputable def nearFrame (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V))
    (dis : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12) :
    NearOwnerFrame G S X := by
  classical
  let M := S.filter (fun u => (singlesFor G S X u).Nonempty)
  let D := weightedSet X (Dcol G S)
  let leaf (u : V) := if h : u∈M then Classical.choose ((Finset.mem_filter.mp h).2 :
    (singlesFor G S X u).Nonempty) else u
  refine ⟨M,D,leaf,Finset.filter_subset _ _,?_,?_⟩
  · intro u hu
    have x : leaf u ∈ singlesFor G S X u := by
      unfold leaf
      rw [dif_pos hu]
      exact Classical.choose_spec _
    have hx := (mem_singlesFor G).mp x
    have block (v : V) (hv : v∈X) := all_exterior_blocked_12 G S sc upper v
      (Finset.disjoint_left.mp dis hv)
    obtain ⟨ul,_,_⟩ := singlesFor_ownership G sym irr S X sf block u (leaf u) x
    have one : (ns (G:=G) S (leaf u)).card=1 := hx.2.1
    have eq := Finset.eq_of_subset_of_card_le
      (show ({u}:Finset V) ⊆ ns (G:=G) S (leaf u) from
        fun z hz => Finset.mem_singleton.mp hz ▸ hx.2.2) (by simp [one])
    refine ⟨hx.1,?_ ,?_⟩
    · exact ul
    · intro t ht he
      have hmem := (mem_ns (G:=G) S (leaf u)).mpr ⟨ht,he⟩
      rw [←eq] at hmem
      exact hmem
  · intro z hz
    obtain ⟨zx,e⟩ := Finset.mem_filter.mp hz
    have two : (ns (G:=G) S z).card=2 := (show Dcol G S z from e).1
    have twoL : (ls (G:=G) S z).card=2 := (show Dcol G S z from e).2
    obtain ⟨a,b,ab,h⟩ := Finset.card_eq_two.mp two
    have eq := Finset.eq_of_subset_of_card_le (lone_support_subset (G:=G) S z)
      (show (ns (G:=G) S z).card≤(ls (G:=G) S z).card by omega)
    have al : a∈ls (G:=G) S z := by rw [eq,h]; simp
    have bl : b∈ls (G:=G) S z := by rw [eq,h]; simp
    obtain ⟨aS,la⟩ := (mem_ls (G:=G) S z).mp al
    obtain ⟨bS,lb⟩ := (mem_ls (G:=G) S z).mp bl
    have eS : support G S z=ns (G:=G) S z := by ext u; simp [support,Support]
    exact ⟨zx,a,aS,b,bS,ab,lone_symm G sym la,lone_symm G sym lb,eS.trans h⟩

theorem nearFrame_count_marks (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V))
    (dis : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12) :
    (nearFrame G S X sym irr tf sc sf dis upper).marks.card=acnt G S X := by
  classical
  let blocked (x : V) (hx : x∈X) := all_exterior_blocked_12 G S sc upper x
    (Finset.disjoint_left.mp dis hx)
  have one (u : V) (hu : u∈S) : (singlesFor G S X u).card≤1 := by
    have h0 := degreeTwelve_private_capacity_h13 G sym irr tf S X sc sf dis upper u hu
    have hL := privatePool_isolated G sym S X sf dis blocked u
    have hqi := Finset.card_le_card hL.1
    have hAq := Finset.card_le_card (show singlesFor G S X u ⊆ lonePrivatePool G S X u from
      fun x hx => (singlesFor_ownership G sym irr S X sf blocked u x hx).2.2)
    omega
  change (S.filter (fun u => (singlesFor G S X u).Nonempty)).card=acnt G S X
  unfold acnt
  rw [←singlesFor_sum G S X,← Nat.one_mul ((S.filter (fun u => (singlesFor G S X u).Nonempty)).card)]
  symm
  have h := (indicator_count_flexible S _ 1 (fun u => (singlesFor G S X u).card)
    (fun u hu h => by have hh := Finset.card_pos.mpr h; have h1 := one u hu; omega)
    (fun u hu h => Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h))).symm
  have he : weightedSet S (fun u => (singlesFor G S X u).Nonempty) =
      S.filter (fun u => (singlesFor G S X u).Nonempty) := by
    ext u
    simp [weightedSet]
  rwa [he] at h

#print axioms nearFrame
#print axioms nearFrame_count_marks
end Erdos151N62
