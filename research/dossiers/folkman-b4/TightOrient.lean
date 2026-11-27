import TightShoreLift

namespace FolkmanB4.Tight
variable {L V : Type*} [Fintype L] [Fintype V]

omit [Fintype L] [Fintype V] in
theorem transpose_covered {I : L → V → Prop} (h : Covered I) :
    Covered (fun a b => I b a) := by
  intro v l e
  obtain ⟨m,ml,hm⟩ := h l v e
  exact ⟨m.symm,m.symm_apply_eq.mpr ml.symm,fun j => by simpa using hm (m.symm j)⟩

theorem transpose_tight {I : L → V → Prop} {A : L → Bool} {B : V → Bool}
    (h : Tight I A B) : Tight (fun a b => I b a) B A := by
  intro m hm
  have support (v : V) : I (m.symm v) v := by simpa using hm (m.symm v)
  obtain ⟨w,ww,uniq⟩ := h m.symm support
  refine ⟨m.symm w,?_,?_⟩
  · simpa using ww.symm
  · intro l hl
    have cross : A (m.symm (m l)) ≠ B (m l) := by simpa using hl.symm
    exact (m.symm_apply_eq.mpr (uniq (m l) cross).symm).symm

theorem can_orient {I : L → V → Prop} {A : L → Bool} {B : V → Bool}
    (covered : Covered I) (tight : Tight I A B)
    (existsM : ∃ m : V ≃ L, ∀ v, I (m v) v) :
    Inward I A B ∨ Inward (fun a b => I b a) B A := by
  obtain ⟨m,M⟩ := existsM
  obtain ⟨v,C,_⟩ := tight m M
  have direction (l : L) (u : V) (e : I l u) (d : A l≠B u) :
      bitZ (A l)-bitZ (B u)=bitZ (A (m v))-bitZ (B v) :=
    one_cut_direction I A B covered tight e (M v) d C
  cases q : A (m v) <;> cases r : B v
  · exact False.elim (C (q.trans r.symm))
  · right
    intro u l hu hl
    by_contra bad
    have hf : B u=false := by cases h : B u <;> simp [h] at bad ⊢
    have dis : A l≠B u := by simp [hl,hf]
    have J := direction l u hu dis
    simp [q,r,hl,hf,bitZ] at J
  · left
    intro l u hu hl
    by_contra bad
    have hf : A l=false := by cases h : A l <;> simp [h] at bad ⊢
    have dis : A l≠B u := by simp [hl,hf]
    have J := direction l u hu dis
    simp [q,r,hl,hf,bitZ] at J
  · exact False.elim (C (q.trans r.symm))

#print axioms can_orient
#print axioms transpose_covered
#print axioms transpose_tight
end FolkmanB4.Tight
