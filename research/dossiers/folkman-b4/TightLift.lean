import TightContract

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V]

def pointsContraction (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (l : In A) : Option (In B) → Prop
  | none => ∃ v, B v=false ∧ I l.val v
  | some v => I l.val v.val

/-- The inward orientation property records that no original matched
inside column can be paired to an outside row. -/
def Inward (I : L → V → Prop) (A : L → Bool) (B : V → Bool) : Prop :=
  ∀ l v, I l v → B v=true → A l=true

def Tight (I : L → V → Prop) (A : L → Bool) (B : V → Bool) : Prop :=
  ∀ m : V ≃ L, (∀ v, I (m v) v) → ∃! v, A (m v)≠B v

def Covered (I : L → V → Prop) : Prop :=
  ∀ l v, I l v → ∃ m : V ≃ L, m v=l ∧ ∀ w, I (m w) w

/-- A matching in the contraction lifts while using any original edge
represented by its selected contracted-port incidence. -/
theorem lift_from_port (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (covered : Covered I) (tight : Tight I A B)
    (q : Option (In B) ≃ In A)
    (Q : ∀ z, pointsContraction I A B (q z) z)
    (u : V) (out : B u=false) (orig : I (q none).val u) :
    ∃ n : V ≃ L, (∀ v, I (n v) v) ∧
      (∀ v : In B, n v.val=(q (some v)).val) ∧ n u=(q none).val := by
  obtain ⟨m,mu,hm⟩ := covered _ _ orig
  obtain ⟨v,cv,uv⟩ := tight m hm
  have inside : A (m u)=true := mu.symm ▸ (q none).property
  have cross : A (m u)≠B u := by simp [inside,out]
  have ueq : u=v := uv _ cross
  have unique (w : V) (c : A (m w)≠B w) : w=u := (uv _ c).trans ueq.symm
  obtain ⟨n,hn,ni,no⟩ := lift_quotient_matching I A B m u out hm inside unique q mu.symm
    (fun v => Q (some v))
  exact ⟨n,hn,ni,(no u out).trans mu⟩

/-- Every perfect matching of the original projects to a supported perfect
matching of the contraction. -/
theorem project_original (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (inward : Inward I A B) (tight : Tight I A B)
    (m : V ≃ L) (hm : ∀ v, I (m v) v) :
    ∃ q : Option (In B) ≃ In A,
      (∀ z, pointsContraction I A B (q z) z) ∧
      ∀ v : In B, (q (some v)).val=m v.val := by
  obtain ⟨u,cu,unique⟩ := tight m hm
  have out : B u=false := by
    cases h : B u
    · rfl
    · exact False.elim (cu ((inward _ _ (hm u) h).trans h.symm))
  have port : A (m u)=true := by
    cases h : A (m u)
    · exact False.elim (cu (h.trans out.symm))
    · rfl
  let fn := projected A B m u (fun w hw => inward _ _ (hm w) hw) port
  let q := Equiv.ofBijective fn (projected_bijective A B m u out _ port unique)
  refine ⟨q,?_,fun v => rfl⟩
  intro z
  cases z with
  | none => exact ⟨u,out,hm u⟩
  | some v => exact hm v.val

/-- A matching-covered graph has a matching-covered contraction, with
parallel ports collapsed to adjacency for this statement. -/
theorem contraction_covered (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (inward : Inward I A B) (tight : Tight I A B) (cover : Covered I) :
    Covered (pointsContraction I A B) := by
  intro l v h
  cases v with
  | none =>
    obtain ⟨u,out,edge⟩ := h
    obtain ⟨m,mu,hm⟩ := cover l.val u edge
    have inside : A (m u)=true := mu.symm ▸ l.property
    have cu : A (m u)≠B u := by simp [inside,out]
    obtain ⟨v,cv,uniq⟩ := tight m hm
    have unique (w : V) (hw : A (m w)≠B w) : w=u := (uniq _ hw).trans (uniq _ cu).symm
    let q := Equiv.ofBijective (projected A B m u (fun w hw => inward _ _ (hm w) hw) inside)
      (projected_bijective A B m u out _ inside unique)
    refine ⟨q,Subtype.ext mu,?_⟩
    intro p
    cases p with
    | none => exact ⟨u,out,hm u⟩
    | some w => exact hm w.val
  | some v =>
    obtain ⟨m,mu,hm⟩ := cover l.val v.val h
    obtain ⟨q,Q,eq⟩ := project_original I A B inward tight m hm
    exact ⟨q,Subtype.ext ((eq v).trans mu),Q⟩

#print axioms lift_from_port
#print axioms project_original
#print axioms contraction_covered
end FolkmanB4.Tight
