import TightExpansion

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

theorem robust_two_extend (I : L → V → Prop) [DecidableRel I] (H : NoSmallCut I)
    (M : ∃ m : V ≃ L, ∀ v, I (m v) v)
    {a b : L} {x y : V} (hab : a≠b) (hxy : x≠y) (ax : I a x) (by' : I b y) :
    ∃ m : V ≃ L, m x=a ∧ m y=b ∧ ∀ v, I (m v) v := by
  classical
  let A : Finset L := {a,b}
  let B : Finset V := {x,y}
  let N (v : {v : V // v∉B}) : Finset {l : L // l∉A} :=
    univ.filter (fun l => I l.val v.val)
  have cardA : A.card=2 := by simp [A,hab]
  have cardB : B.card=2 := by simp [B,hxy]
  have T (S : Finset {v : V // v∉B}) : S.card≤(S.biUnion N).card := by
    by_cases z : S=∅
    · simp [z]
    let t := S.image Subtype.val
    have eq : t.card=S.card := card_image_of_injective _ Subtype.val_injective
    have incl : t⊆univ \ B := by
      intro v hv
      obtain ⟨u,_,rfl⟩ := mem_image.mp hv
      exact mem_sdiff.mpr ⟨mem_univ _,u.property⟩
    have bound := card_le_card incl
    rw [card_sdiff_of_subset (subset_univ _),card_univ,cardB] at bound
    have total : 2≤Fintype.card V := by simpa [cardB] using card_le_card (subset_univ B)
    have h := robust_hall I H M t (by rw [eq]; exact card_pos.mpr (nonempty_iff_ne_empty.mpr z))
      (by omega)
    have img : (S.biUnion N).image Subtype.val = t.biUnion (rows I) \ A := by
      ext l
      simp only [mem_image,mem_biUnion,mem_sdiff,rows,N,t,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨u,⟨v,hv,adj⟩,rfl⟩
        exact ⟨⟨v.val,⟨v,hv,rfl⟩,adj⟩,u.property⟩
      · rintro ⟨⟨v,⟨w,hw,rfl⟩,adj⟩,out⟩
        exact ⟨⟨l,out⟩,⟨w,hw,adj⟩,rfl⟩
    have k := le_card_sdiff A (t.biUnion (rows I))
    rw [←img,card_image_of_injective _ Subtype.val_injective] at k
    omega
  obtain ⟨f,inj,hf⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp T
  let g (v : V) : L :=
    if h : v∈B then (if v=x then a else b) else (f ⟨v,h⟩).val
  have gi : Function.Injective g := by
    intro u v e
    by_cases hu : u∈B <;> by_cases hv : v∈B
    · have k (w : V) (hw : w∈B) : w=x ∨ w=y := by simpa [B] using hw
      rcases k u hu with rfl|rfl <;> rcases k v hv with rfl|rfl <;>
        simp_all [g,B,Ne.symm hxy,Ne.symm hab]
    · have k : g u∈A := by simp only [g,dif_pos hu]; split <;> simp [A]
      have l : g v∉A := by simpa [g,hv] using (f ⟨v,hv⟩).property
      exact False.elim (l (e ▸ k))
    · have k : g v∈A := by simp only [g,dif_pos hv]; split <;> simp [A]
      have l : g u∉A := by simpa [g,hu] using (f ⟨u,hu⟩).property
      exact False.elim (l (e.symm ▸ k))
    · exact congrArg Subtype.val (inj (Subtype.ext (by simpa [g,hu,hv] using e)))
  obtain ⟨m,hm⟩ := M
  let q := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨gi,Fintype.card_congr m⟩)
  refine ⟨q,by simp [q,g,B],by simp [q,g,B,Ne.symm hxy],?_⟩
  intro v
  change I (g v) v
  by_cases h : v∈B
  · have k : v=x ∨ v=y := by simpa [B] using h
    rcases k with rfl|rfl
    · simpa [g,B] using ax
    · simpa [g,B,Ne.symm hxy] using by'
  · simpa [g,h,N] using hf ⟨v,h⟩

#print axioms robust_two_extend
end FolkmanB4.Tight
