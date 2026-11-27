import TightSquare
import Mathlib.GroupTheory.Perm.Option

namespace FolkmanB4.Tight
open Critical
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq V]

theorem sign_difference {W Z : Type*} [Fintype W] [DecidableEq W]
    (k s t : W ≃ Z) (eq : pSign (s.trans k.symm)=pSign (t.trans k.symm)) :
    Equiv.Perm.sign (s.trans t.symm)=1 := by
  let a := s.trans k.symm
  let b := t.trans k.symm
  have sa : Equiv.Perm.sign a=Equiv.Perm.sign b := by
    have e : ((Equiv.Perm.sign a : Int) : ℚ)=((Equiv.Perm.sign b : Int):ℚ) := eq
    have f : (Equiv.Perm.sign a : Int)=(Equiv.Perm.sign b : Int) := by exact_mod_cast e
    exact Units.ext f
  have e : s.trans t.symm=a.trans b.symm := by ext x; simp [a,b]
  rw [e,Equiv.Perm.sign_trans,Equiv.Perm.sign_symm,sa]
  simp

/-- Quotient matchings using a common port retain their relative matching
parity after gluing to one fixed matching of the complementary shore. -/
theorem quotient_fixed_port_parity (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (covered : Covered I) (tight : Tight I A B)
    (k : V ≃ L)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm))
    (q r : Option (In B) ≃ In A)
    (Q : ∀ i, pointsContraction I A B (q i) i)
    (R : ∀ i, pointsContraction I A B (r i) i)
    (same : q none=r none) : Equiv.Perm.sign (q.trans r.symm)=1 := by
  classical
  obtain ⟨u,out,orig⟩ := Q none
  obtain ⟨m,mu,hm⟩ := covered _ u orig
  have inside : A (m u)=true := mu.symm ▸ (q none).property
  have cross : A (m u)≠B u := by simp [inside,out]
  obtain ⟨v,_,uv⟩ := tight m hm
  have unique (w : V) (c : A (m w)≠B w) : w=u := (uv _ c).trans (uv _ cross).symm
  obtain ⟨s,hs,si,so⟩ :=
    lift_quotient_matching I A B m u out hm inside unique q mu.symm (fun z => Q (some z))
  have rp : (r none).val=m u := by rw [←same,mu]
  obtain ⟨t,ht,ti,tout⟩ :=
    lift_quotient_matching I A B m u out hm inside unique r rp (fun z => R (some z))
  have par := sign_difference k s t (signs s t hs ht)
  let delta := q.trans r.symm
  have z : delta none=none := by
    change r.symm (q none)=none
    rw [same,r.symm_apply_apply]
  let sub := delta.removeNone
  have sub_eq : sub.optionCongr=delta := by
    have h := map_equiv_removeNone delta
    rw [z,Equiv.swap_self] at h
    change sub.optionCongr = 1 * delta at h
    simpa only [one_mul] using h
  have E : s.trans t.symm = Equiv.Perm.ofSubtype sub := by
    ext w
    by_cases wi : B w=true
    · let w' : In B := ⟨w,wi⟩
      have D : delta (some w')=some (sub w') := by
        rw [←sub_eq]; rfl
      have rowEq : q (some w')=r (some (sub w')) := by
        apply r.symm.injective
        simpa [delta] using D
      rw [Equiv.Perm.ofSubtype_apply_of_mem (p:=fun v : V => B v=true) (a:=w) sub wi]
      change t.symm (s w)=_
      apply t.injective
      rw [t.apply_symm_apply]
      exact (si w').trans ((congrArg Subtype.val rowEq).trans (ti (sub w')).symm)
    · have wf : B w=false := by cases h : B w <;> simp [h] at wi ⊢
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem (p:=fun v : V => B v=true) (a:=w) sub wi]
      change t.symm (s w)=w
      apply t.injective
      rw [t.apply_symm_apply,so w wf,tout w wf]
  change Equiv.Perm.sign delta=1
  rw [←sub_eq,Equiv.optionCongr_sign]
  rwa [E,Equiv.Perm.sign_ofSubtype] at par

#print axioms quotient_fixed_port_parity
end FolkmanB4.Tight
