import N62PrivateExact
import N62DoubleStar

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

/-- A B-column has two adjacent owners, not merely two incidences. -/
theorem Bcol_adjacent_support
    (S : Finset V) (x : V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sf : Free (Forbidden G) (S : Set V))
    (blocked : ¬Free (Forbidden G) (insert x (S : Set V)))
    (b : Bcol G S x) :
    ∃ u∈S, ∃ v∈S, u≠v ∧ G u v ∧ G u x ∧ G v x ∧ support G S x={u,v} := by
  classical
  rcases blocked_witness (G := G) (S:=↑S) (x:=x) sym irr sf blocked with
    ⟨a,ha,hl⟩ | ⟨a,ha,c,hc,ne,ac⟩
  · have h := Finset.card_pos.mpr ⟨a,(mem_ls (G:=G) S x).mpr ⟨ha.1,hl⟩⟩
    have hz : (ls (G:=G) S x).card=0 := b.2
    omega
  · have hns : ({a,c} : Finset V)⊆ns (G:=G) S x := by
      intro u hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl|rfl
      · exact (mem_ns (G:=G) S x).mpr ha
      · exact (mem_ns (G:=G) S x).mpr hc
    have eq := Finset.eq_of_subset_of_card_le hns (by
      change (ns (G:=G) S x).card≤({a,c}:Finset V).card
      have h := b.1
      change (ns (G:=G) S x).card=2 at h
      simp [h,Finset.card_insert_of_notMem,ne])
    refine ⟨a,ha.1,c,hc.1,ne,ac,sym ha.2,sym hc.2,?_⟩
    have f : support G S x=ns (G:=G) S x := by ext v; simp [support,Support]
    exact f.trans eq.symm

/-- Charged support slots use n for A/B and l for C; the second
charge uses l for A/C only. Thus one B hits each of two endpoints,
whereas A and C hit their unique lone owner twice. -/
noncomputable def privateFirst (S X : Finset V) (u : V) : Finset V := by
  classical exact X.filter (fun x =>
    ((Acol G S x ∨ Bcol G S x) ∧ u∈ns (G:=G) S x) ∨
    (Ccol G S x ∧ u∈ls (G:=G) S x))

noncomputable def privateSecond (S X : Finset V) (u : V) : Finset V := by
  classical exact X.filter (fun x => (Acol G S x ∨ Ccol G S x) ∧ u∈ls (G:=G) S x)

theorem private_slots_charged
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (dis : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (u : V) (hu : u∈S) :
    (privateFirst G S X u).card+(privateSecond G S X u).card≤2 := by
  classical
  have lone_charge (x : V) (hx : x∈X) (a : Acol G S x ∨ Ccol G S x)
      (ul : u∈ls (G:=G) S x) : u∈qs (G:=G) S x := by
    have small : (ns (G:=G) S x).card≤2 := by
      rcases a with ha|hc
      · exact Nat.le_of_eq (show (ns (G:=G) S x).card=1 from ha) |>.trans (by decide)
      · exact Nat.le_of_eq hc.1
    have lc : (ls (G:=G) S x).card=1 := by
      rcases a with ha|hc
      · exact (blocked_one_lone (G:=G) S x sym irr sf
          (all_exterior_blocked_12 G S sc upper x (Finset.disjoint_left.mp dis hx)) ha).1
      · exact hc.2
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp lc
    have hh : u=v := by simpa [hv] using ul
    have hp := owner_of_small_support (G:=G) S x sym irr sf (lone_support_subset (G:=G) S x ul)
      small (fun z hz => (Finset.mem_singleton.mp (hv ▸ hz)).trans hh.symm)
    obtain ⟨_,l⟩ := (mem_ls (G:=G) S x).mp ul
    exact (mem_qs (G:=G) S x).mpr ⟨hu,l,(mem_ps (G:=G) S x).mp hp |>.2⟩
  have fst : privateFirst G S X u⊆privatePool G S X u := by
    intro x hx
    obtain ⟨he,h⟩ := Finset.mem_filter.mp hx
    apply (mem_privatePool G).mpr
    refine ⟨he,?_⟩
    rcases h with ⟨t,un⟩|⟨t,ul⟩
    · rcases t with a|b
      · have lc := (blocked_one_lone (G:=G) S x sym irr sf
          (all_exterior_blocked_12 G S sc upper x (Finset.disjoint_left.mp dis he)) a).1
        have nsOne : (ns (G:=G) S x).card=1 := a
        have eq := Finset.eq_of_subset_of_card_le (lone_support_subset (G:=G) S x)
          (show (ns (G:=G) S x).card≤(ls (G:=G) S x).card by omega)
        have hq := (mem_qs (G:=G) S x).mp (lone_charge x he (Or.inl a) (eq.symm ▸ un))
        exact (mem_ps (G:=G) S x).mpr ⟨hu,hq.2.2⟩
      · apply owner_of_small_support (G:=G) S x sym irr sf un (by exact Nat.le_of_eq b.1)
        intro z hz
        have h := Finset.card_pos.mpr ⟨z,hz⟩
        have zero : (ls (G:=G) S x).card=0 := b.2
        omega
    · have hq := (mem_qs (G:=G) S x).mp (lone_charge x he (Or.inr t) ul)
      exact (mem_ps (G:=G) S x).mpr ⟨hu,hq.2.2⟩
  have snd : privateSecond G S X u⊆lonePrivatePool G S X u := by
    intro x hx
    obtain ⟨he,t,ul⟩ := Finset.mem_filter.mp hx
    exact (mem_lonePrivatePool G).mpr ⟨he, lone_charge x he t ul⟩
  have h := degreeTwelve_private_capacity_h13 G sym irr tf S X sc sf dis upper u hu
  have p := Finset.card_le_card fst
  have q := Finset.card_le_card snd
  omega

#print axioms Bcol_adjacent_support
#print axioms private_slots_charged
end Erdos151N62
