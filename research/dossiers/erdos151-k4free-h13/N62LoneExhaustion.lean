import N62NearStar
import N62GraphPrivateCases

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem exhausted_lone_class
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sf : Free (Forbidden G) (S : Set V))
    (blocked : ∀ x∈X, ¬Free (Forbidden G) (insert x (S : Set V)))
    (eq : ∑ x∈X,lcol G S x=acnt G S X+ccnt G S X+2*dcnt G S X)
    {x : V} (xx : x∈X) (pos : 0<lcol G S x) :
    Acol G S x ∨ Ccol G S x ∨ Dcol G S x := by
  classical
  let a (x : V) := if Acol G S x then (1:Nat) else 0
  let c (x : V) := if Ccol G S x then (1:Nat) else 0
  let d (x : V) := if Dcol G S x then (2:Nat) else 0
  have h (z : V) (hz : z∈X) : a z+c z+d z≤lcol G S z := by
    have hh := (blocked_degreeTen_local G S sym irr sf z (blocked z hz)).2.2.1
    change a z + c z + 2*(if Dcol G S z then 1 else 0) ≤ _ at hh
    by_cases hd : Dcol G S z <;> simpa [d,hd] using hh
  by_contra! bad
  have less : a x + c x + d x < lcol G S x := by simp [a,c,d,bad.1,bad.2.1,bad.2.2,pos]
  have lt := sum_lt_sum h ⟨x,xx,less⟩
  simp only [sum_add_distrib] at lt
  have aa : acnt G S X=∑ z∈X,a z := by
    simpa [acnt,a] using indicator_count X (Acol G S) 1
  have cc : ccnt G S X=∑ z∈X,c z := by
    simpa [ccnt,c] using indicator_count X (Ccol G S) 1
  have dd : 2*dcnt G S X=∑ z∈X,d z := by
    exact indicator_count X (Dcol G S) 2
  omega

theorem marked_private_full
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (dis : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {u : V} (um : u∈(nearFrame G S X sym irr tf sc sf dis upper).marks) :
    let F := nearFrame G S X sym irr tf sc sf dis upper
    privateFirst G S X u={F.leaf u} ∧ privateSecond G S X u={F.leaf u} := by
  classical
  let F := nearFrame G S X sym irr tf sc sf dis upper
  have aData : F.leaf u∈singlesFor G S X u := by
    change (if h : u∈F.marks then Classical.choose ((mem_filter.mp h).2 :
      (singlesFor G S X u).Nonempty) else u)∈singlesFor G S X u
    rw [dif_pos um]
    exact Classical.choose_spec _
  have hb := (mem_singlesFor G).mp aData
  have r := F.leafData u um
  have l : u∈ls (G:=G) S (F.leaf u) :=
    (mem_ls (G:=G) S _).mpr ⟨F.markSub um,lone_symm G sym r.2.1⟩
  have fs : F.leaf u∈privateFirst G S X u :=
    mem_filter.mpr ⟨hb.1,Or.inl ⟨Or.inl hb.2.1,hb.2.2⟩⟩
  have ss : F.leaf u∈privateSecond G S X u :=
    mem_filter.mpr ⟨hb.1,Or.inl hb.2.1,l⟩
  have c := private_slots_charged G S X sym irr tf sc sf dis upper u (F.markSub um)
  have c1 := card_pos.mpr ⟨_,fs⟩
  have c2 := card_pos.mpr ⟨_,ss⟩
  have e1 : (privateFirst G S X u).card≤({F.leaf u}:Finset V).card := by simp; omega
  have e2 : (privateSecond G S X u).card≤({F.leaf u}:Finset V).card := by simp; omega
  exact ⟨(eq_of_subset_of_card_le (singleton_subset_iff.mpr fs) e1).symm,
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr ss) e2).symm⟩

#print axioms exhausted_lone_class
#print axioms marked_private_full
end Erdos151N62
