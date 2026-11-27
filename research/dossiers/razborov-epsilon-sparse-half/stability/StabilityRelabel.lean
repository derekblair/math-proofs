import StabilityRepair

open scoped BigOperators
namespace SparseHalfStability

variable {V I T : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def bad (G : V → V → Bool) (H : I → I → Bool) (p : V → I) (τ : ℝ) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v => τ < ((err G H p v).card : ℝ)

theorem bad_size (G : V → V → Bool) (H : I → I → Bool) (p : V → I)
    (τ : ℝ) (hp : 0 < τ) (budget : ((directedErrors G H p).card : ℝ) ≤ τ^2) :
    ((bad G H p τ).card : ℝ) ≤ τ := by
  classical
  let D := bad G H p τ
  let f : Sigma (fun _ : V => V) → V × V := fun e => (e.1,e.2)
  have ha := Finset.card_le_card_of_injOn
    (s := D.sigma (err G H p)) (t := directedErrors G H p) f (by
      intro e he
      change f e ∈ directedErrors G H p
      have h := (Finset.mem_sigma.mp (show e ∈ D.sigma (err G H p) from he)).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      exact (Finset.mem_filter.mp h).2) (by
      intro a _ b _ h
      cases a
      cases b
      cases h
      rfl)
  rw [Finset.card_sigma] at ha
  have hA : (∑ v ∈ D, ((err G H p v).card : ℝ)) ≤ (directedErrors G H p).card := by
    exact_mod_cast ha
  have hB : (D.card : ℝ)*τ ≤ ∑ v ∈ D, ((err G H p v).card : ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      (Finset.sum_le_sum (s := D) fun v hv => (Finset.mem_filter.mp hv).2.le)
  exact le_of_mul_le_mul_right (hB.trans (hA.trans (by simpa [pow_two] using budget))) hp

def extras (G : V → V → Bool) (B : T → T → Bool) (q : V → T) (v : V) : Finset V :=
  Finset.univ.filter fun x => G v x = true ∧ B (q v) (q x) = false

theorem exterior_count (G : V → V → Bool) (B : T → T → Bool)
    (p : V → I) (q : V → T) (embed : I → T) (D : Finset V)
    (go : ∀ v ∉ D, q v = embed (p v)) (τ : ℝ) (hτ : 0 ≤ τ)
    (ad : ∀ v ∈ D, ∀ i ∈ heavy G p τ v, B (q v) (embed i) = true)
    (v : V) (hv : v ∈ D) :
    (((extras G B q v \ D).card : ℝ)) ≤ (Fintype.card I : ℝ)*τ := by
  let A (i : I) := (extras G B q v \ D).filter (fun x => p x = i)
  let f (x : V) : Sigma (fun _ : I => V) := ⟨p x,x⟩
  have hx := Finset.card_le_card_of_injOn
    (s := extras G B q v \ D) (t := Finset.univ.sigma A) f (by
      intro x h
      change f x ∈ Finset.univ.sigma A
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨h,rfl⟩⟩)
    (by intro a _ b _ h; exact congrArg (fun e : Sigma (fun _ : I => V) => e.2) h)
  rw [Finset.card_sigma] at hx
  have hx' : ((extras G B q v \ D).card : ℝ) ≤ ∑ i, ((A i).card : ℝ) := by
    exact_mod_cast hx
  have hb (i : I) : ((A i).card : ℝ) ≤ τ := by
    by_cases hi : i ∈ heavy G p τ v
    · have h0 : A i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hx1,hp⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx2,hd⟩ := Finset.mem_sdiff.mp hx1
        have hB := (Finset.mem_filter.mp hx2).2.2
        rw [go x hd, hp, ad v hv i hi] at hB
        exact Bool.noConfusion hB
      simp [h0,hτ]
    · have hA : A i ⊆ near G p v i := by
        intro x hx
        obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hx
        have hg := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).2.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩,hg⟩
      have hh : ((A i).card : ℝ) ≤ (near G p v i).card := by
        exact_mod_cast Finset.card_le_card hA
      apply hh.trans
      apply le_of_not_gt
      intro h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  exact hx'.trans (by simpa only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
    using Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hb i))

#print axioms bad_size
#print axioms exterior_count
end SparseHalfStability
