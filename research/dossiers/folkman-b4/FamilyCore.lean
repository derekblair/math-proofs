import MinimalFamily
import CentralSquare

namespace FolkmanB4
open Finset Critical

variable {E : Type*} [DecidableEq E]

def points (S : Finset (Finset E)) : Finset E := S.biUnion id
abbrev Point (S : Finset (Finset E)) := {e : E // e ∈ points S}
abbrev Line (S : Finset (Finset E)) := {t : Finset E // t∈S}

instance (S : Finset (Finset E)) : Fintype (Point S) := Fintype.ofFinset _ (fun _ => Iff.rfl)
instance (S : Finset (Finset E)) : Fintype (Line S) := Fintype.ofFinset _ (fun _ => Iff.rfl)

def inc (S : Finset (Finset E)) (t : Line S) (e : Point S) : Prop := e.val∈t.val

instance (S : Finset (Finset E)) : DecidableRel (inc S) :=
  fun t e => inferInstanceAs (Decidable (e.val ∈ t.val))

theorem mem_points {S : Finset (Finset E)} {e : E} :
    e∈points S ↔ ∃ t∈S,e∈t := by simp [points]

theorem point_degree (S : Finset (Finset E)) (t : Line S) : pts (inc S) t=t.val.card := by
  let M := (univ.filter (inc S t)).map (Function.Embedding.subtype (fun e => e∈points S))
  have eq : M=t.val := by
    ext e
    constructor
    · intro h
      obtain ⟨q,hq,hqe⟩ := mem_map.mp h
      exact hqe ▸ (mem_filter.mp hq).2
    · intro h
      exact mem_map.mpr ⟨⟨e,mem_points.mpr ⟨t.val,t.property,h⟩⟩,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  rw [←eq,card_map]
  rfl

theorem line_degree (S : Finset (Finset E)) (e : Point S) :
    lns (inc S) e=(S.filter fun t => e.val∈t).card := by
  let M := (univ.filter fun t : Line S => inc S t e).map
    (Function.Embedding.subtype (fun t => t∈S))
  have eq : M=S.filter (fun t => e.val∈t) := by
    ext t
    constructor
    · intro h
      obtain ⟨q,hq,hqt⟩ := mem_map.mp h
      exact hqt ▸ mem_filter.mpr ⟨q.property,(mem_filter.mp hq).2⟩
    · intro h
      obtain ⟨ts,ei⟩ := mem_filter.mp h
      exact mem_map.mpr ⟨⟨t,ts⟩,mem_filter.mpr ⟨mem_univ _,ei⟩,rfl⟩
  rw [←eq,card_map]
  rfl

theorem inc_used (S : Finset (Finset E)) (e : Point S) : ∃ t, inc S t e := by
  obtain ⟨t,ts,et⟩ := mem_points.mp e.property
  exact ⟨⟨t,ts⟩,et⟩

theorem split_of_good {S : Finset (Finset E)} {c : Point S → Bool}
    (h : Good (inc S) univ c) : Splittable S := by
  let C (e : E) := if w : e∈points S then c ⟨e,w⟩ else false
  refine ⟨C,fun t ts => ?_⟩
  obtain ⟨⟨a,ai,ac⟩,⟨b,bi,bc⟩⟩ := h ⟨t,ts⟩ (mem_univ _)
  exact ⟨⟨a.val,ai,by simp [C,a.property,ac]⟩,⟨b.val,bi,by simp [C,b.property,bc]⟩⟩

theorem proper_lift {S : Finset (Finset E)}
    (h : ∀ T, T ⊂ S → Splittable T) (R : Finset (Line S)) (p : R≠univ) :
    ∃ c, Good (inc S) R c := by
  let emb := Function.Embedding.subtype (fun t => t∈S)
  let T := R.map emb
  have sub : T⊆S := by
    intro t ht
    obtain ⟨k,_,e⟩ := mem_map.mp ht
    exact e ▸ k.property
  have ne : T≠S := by
    intro eq
    apply p
    apply eq_univ_of_forall
    intro k
    have km : k.val∈T := eq.symm ▸ k.property
    obtain ⟨l,lr,lv⟩ := mem_map.mp km
    exact Subtype.ext lv ▸ lr
  obtain ⟨c,hc⟩ := h T (Finset.ssubset_iff_subset_ne.mpr ⟨sub,ne⟩)
  refine ⟨fun e => c e.val, fun t tr => ?_⟩
  obtain ⟨⟨a,ha,ac⟩,⟨b,bt,bc⟩⟩ := hc t.val (mem_map.mpr ⟨t,tr,rfl⟩)
  exact ⟨⟨⟨a,mem_points.mpr ⟨t.val,t.property,ha⟩⟩,ha,ac⟩,
    ⟨⟨b,mem_points.mpr ⟨t.val,t.property,bt⟩⟩,bt,bc⟩⟩

theorem family_core {T : Finset (Finset E)}
    (row : ∀ t∈T, t.card=3) (degree : ∀ e : E, (T.filter fun t => e∈t).card≤3)
    (h : ¬Splittable T) :
    ∃ S ⊆ T, S.Nonempty ∧ (∀ t : Line S, pts (inc S) t=3) ∧ (∀ e : Point S, lns (inc S) e=3) ∧
      ∃ k : Point S ≃ Line S,
        ∀ s t : Point S ≃ Line S,
        (∀ i, inc S (s i) i) → (∀ i, inc S (t i) i) →
          pSign (s.trans k.symm)=pSign (t.trans k.symm) := by
  classical
  obtain ⟨S,st,bad,min⟩ := minimal_family h
  have R (t : Line S) : pts (inc S) t=3 := (point_degree S t).trans (row t.val (st t.property))
  have C (e : Point S) : lns (inc S) e≤3 := by
    rw [line_degree]
    exact (card_le_card (filter_subset_filter _ st)).trans (degree e.val)
  have B : ¬∃ c, Good (inc S) univ c := by
    rintro ⟨c,g⟩
    exact bad (split_of_good g)
  obtain ⟨d,k⟩ := cubic_and_same_parity (inc S) (inc_used S) B (proper_lift min) R C
  have sn : S.Nonempty := by
    by_contra no
    have empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp no
    subst S
    exact bad ⟨fun _ => false, by simp [Splits]⟩
  exact ⟨S,st,sn,R,d,k⟩

#print axioms family_core
end FolkmanB4
