import BraceTheorem

namespace FolkmanB4
open Finset Critical Tight
universe u
variable {W : Type u} [Fintype W] [DecidableEq W]

theorem structural_from_brace (ext : BraceDichotomy.{u}) : StructuralInput W := by
  classical
  intro S n row col edges sign
  let I := inc S
  have M := regular_perfect_matching I (by decide : 0<3) row col
  obtain ⟨m,hm⟩ := M
  obtain ⟨k,signs⟩ := sign
  have rc (l : Line S) : l.val.card=3 := by
    have E : (univ.filter (fun p : Point S => I l p)).image Subtype.val=l.val := by
      ext p
      simp only [mem_image,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨p,h,rfl⟩
        exact h
      · intro h
        exact ⟨⟨p,mem_points.mpr ⟨l.val,l.property,h⟩⟩,h,rfl⟩
    rw [←E,card_image_of_injective _ Subtype.val_injective]
    exact row l
  by_cases noc : NoSmallCut I
  · obtain ⟨l,hl⟩ := n
    have sz : 3≤Fintype.card (Point S) := by
      have h : pts I ⟨l,hl⟩ ≤ Fintype.card (Point S) := card_le_univ _
      rw [show pts I ⟨l,hl⟩=3 from row ⟨l,hl⟩] at h
      exact h
    rcases ext _ _ I row col sz noc (signable_of_constant I k m hm signs) with H|H
    · obtain ⟨r,c,h⟩ := H
      exact Or.inl (Fano.full_fano_fragment r.toEmbedding c.toEmbedding h rc edges)
    · obtain ⟨p,_,_⟩ := H
      obtain ⟨f,hf,e₁,e₂⟩ := p.central noc ⟨m,hm⟩
      exact False.elim (no_switch_square I k signs f hf p.vne e₁ e₂)
  · obtain ⟨a,b,nt,tight,mini⟩ := min_nontrivial I noc
    have covered : Covered I := fun _ _ h => regular_covers I row col h
    rcases can_orient covered tight ⟨m,hm⟩ with A|B
    · obtain ⟨r,c,h⟩ := heawood_oriented I a b ext row col nt tight A mini k signs
      exact Or.inr (Fano.normalize_point_port _ _ r c h rc edges)
    · let J (p : Point S) (t : Line S) := I t p
      letI : DecidableRel J := fun p t => inferInstanceAs (Decidable (I t p))
      have BS : Tight.Nontrivial b a := by
        simpa only [Tight.Nontrivial,shore,Nat.add_comm] using nt
      have mn (s : Finset (Point S)) (t : Finset (Line S)) (hp : Tight.Nontrivial s t)
          (h : Tight J (fun l => decide (l∈s)) (fun v => decide (v∈t))) :
          shore b a ≤ shore s t := by
        have ht : Tight.Nontrivial t s := by simpa only [Tight.Nontrivial,shore,Nat.add_comm] using hp
        simpa only [shore,Nat.add_comm] using (mini t s ht (transpose_tight h))
      obtain ⟨c,r,h⟩ := heawood_oriented J b a ext col row BS (transpose_tight tight) B mn
        k.symm (same_sign_transpose I k signs)
      let r' := Fano.dual.trans r
      let c' := Fano.dual.trans c
      have hh (l p : Fin 7) : pointsContraction J _ _ (c' p) (r' l) ↔ Fano.inc l p :=
        (h _ _).trans (Fano.self_dual l p)
      exact Or.inl (Fano.normalize_line_port _ _ r' c' hh rc edges)

/-- Exact graph theorem with the only external input stated explicitly. -/
theorem graph_color_of_brace (ext : BraceDichotomy.{u})
    (G : Finset (Finset W)) (book : BookFree G) : Splittable (graphTriangles G) :=
  graph_color_of_structure G book (structural_from_brace ext)

#print axioms graph_color_of_brace
end FolkmanB4
