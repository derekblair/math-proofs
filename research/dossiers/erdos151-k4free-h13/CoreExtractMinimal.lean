import CoreExtract
namespace BikovLocal

/-- Every finite K4-free Ramsey graph contains an edge-minimal Ramsey
core. Isolated vertices may remain in the ambient type, but each vertex
of its actual support has degree at least eight, and each core edge
has two distinct common neighbors. -/
theorem extract_core_minimal {V : Type*} [Fintype V]
    (G : V→V→Prop) (sym : Sym G) (irr : Loopless G) (tl : TriangleFreeLinks G)
    (r : Ramsey G) :
    ∃ C : V→V→Prop, Sub C G ∧ Sym C ∧ Loopless C ∧ TriangleFreeLinks C ∧ Ramsey C ∧
      (∃ a b,C a b) ∧
      (∀ v, (∃ w,C v w) → ∀ [Fintype {w : V // C v w}], 8≤Fintype.card {w : V // C v w}) ∧
      (∀ a b,C a b→TwoThrough C a b) ∧
      (∀ H : V→V→Prop, Sub H C → Sym H →
        ∀ a b, C a b → ¬ H a b → ¬ Ramsey H) := by
  classical
  have ex : ∃ n, ∃ C : V→V→Prop, Sub C G ∧ Sym C ∧ Ramsey C ∧ (directed C).card=n :=
    ⟨_,G,fun {_ _} h=>h,sym,r,rfl⟩
  obtain ⟨C,sub,cs,cr,cc⟩ := Nat.find_spec ex
  have cirr : Loopless C := fun a aa=>irr a (sub aa)
  have ctri : TriangleFreeLinks C := fun v a b c va vb vc ab ac bc=>
    tl v a b c (sub va) (sub vb) (sub vc) (sub ab) (sub ac) (sub bc)
  have less (H : V→V→Prop) (s : Sub H C) (hs : Sym H)
      (a b : V) (ab : C a b) (no : ¬H a b) : ¬Ramsey H := by
    intro hr
    have small := directed_lt H C s a b ab no
    have contra := Nat.find_min' ex (show ∃ C':V→V→Prop,
        Sub C' G ∧ Sym C' ∧ Ramsey C' ∧ (directed C').card=(directed H).card from
          ⟨H,fun {_ _} h=>sub (s h),hs,hr,rfl⟩)
    omega
  have colorable (H : V→V→Prop) (no : ¬Ramsey H) :
      ∃ c : V→V→Bool, (∀ a b,c a b=c b a) ∧ Safe H c := by
    by_contra! n
    apply no
    intro c cs h
    exact n c cs h
  have edge : ∃ a b,C a b := by
    by_contra! n
    have empty : Safe C (fun _ _ => false) := fun a b _ ab _ _ => False.elim (n a b ab)
    exact cr _ (fun _ _=>rfl) empty
  have degree : ∀ v, (∃ w,C v w) → ∀ [Fintype {w : V // C v w}], 8≤Fintype.card {w : V // C v w} := by
    intro v ⟨w,vw⟩ inst
    let H (a b : V) := a≠v ∧ b≠v ∧ C a b
    have s : Sub H C := by intro a b h; exact h.2.2
    have hs : Sym H := by intro a b h; exact ⟨h.2.1,h.1,cs h.2.2⟩
    have no : ¬H v w := fun h=>h.1 rfl
    exact bikov_degree_eight C cs cirr v (ctri v) cr (colorable H (less H s hs v w vw no))
  have book : ∀ a b,C a b→TwoThrough C a b := by
    intro a b ab
    by_contra thin
    let H := Removed C a b
    have s : Sub H C := by intro x y h; exact h.1
    have hs : Sym H := by
      intro x y h
      refine ⟨cs h.1,?_⟩
      rintro (⟨p,q⟩|⟨p,q⟩)
      · exact h.2 (Or.inr ⟨q,p⟩)
      · exact h.2 (Or.inl ⟨q,p⟩)
    have no : ¬H a b := fun h=>h.2 (Or.inl ⟨rfl,rfl⟩)
    obtain ⟨c,csym,ok⟩ := colorable H (less H s hs a b ab no)
    obtain ⟨c',cs',ok'⟩ := extend_thin_edge C cs cirr a b ab thin c csym ok
    exact cr c' cs' ok'
  exact ⟨C,sub,cs,cirr,ctri,cr,edge,degree,book,less⟩


#print axioms extract_core_minimal
end BikovLocal
