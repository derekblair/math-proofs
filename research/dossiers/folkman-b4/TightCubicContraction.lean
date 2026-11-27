import TightDegrees

namespace FolkmanB4.Tight
open Finset Critical
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

theorem no_small_cut_transpose (I : L → V → Prop) (H : NoSmallCut I) :
    NoSmallCut (fun v l => I l v) := by
  intro a b lo hi hm
  exact H b a (by simpa [shore,Nat.add_comm] using lo)
    (by simpa [shore,Nat.add_comm] using hi) (transpose_tight hm)

noncomputable def portMap (B : V → Bool) (v : V) : Option (In B) :=
  if h : B v=true then some ⟨v,h⟩ else none

theorem contraction_neighbors (I : L → V → Prop) [DecidableRel I]
    (A : L → Bool) (B : V → Bool) (l : In A)
    [DecidableRel (pointsContraction I A B)] :
    (univ.filter (fun z => pointsContraction I A B l z)) =
     (univ.filter (fun v => I l.val v)).image (portMap B) := by
  classical
  ext z
  simp only [mem_filter,mem_univ,true_and,mem_image]
  cases z with
  | none =>
    constructor
    · rintro ⟨v,vout,iv⟩
      exact ⟨v,iv,by simp [portMap,vout]⟩
    · rintro ⟨v,iv,e⟩
      have no : B v=false := by
        cases h : B v <;> simp_all [portMap]
      exact ⟨v,no,iv⟩
  | some u =>
    constructor
    · intro h
      exact ⟨u.val,h,by simp [portMap,u.property]⟩
    · rintro ⟨v,iv,e⟩
      have vin : B v=true := by
        cases h : B v <;> simp_all [portMap]
      have r : v=u.val := by
        have e' : some (⟨v,vin⟩ : In B)=some u := by simpa [portMap,vin] using e
        exact congrArg Subtype.val (Option.some.inj e')
      change I l.val u.val
      exact r ▸ iv

theorem cubic_contraction (I : L → V → Prop) [DecidableRel I]
    (S : Finset L) (T : Finset V)
    (large : Nontrivial S T)
    (inward : Inward I (fun l => decide (l∈S)) (fun v => decide (v∈T)))
    (tight : Tight I (fun l => decide (l∈S)) (fun v => decide (v∈T)))
    (mini : ∀ a b, Nontrivial a b →
        Tight I (fun l => decide (l∈a)) (fun v => decide (v∈b)) →
        shore S T ≤ shore a b)
    (row : ∀ l, pts I l = 3) (col : ∀ v, lns I v = 3)
    (M : ∃ m : V ≃ L, ∀ v, I (m v) v) :
    let A (l : L) : Bool := decide (l∈S)
    let B (v : V) : Bool := decide (v∈T)
    let Q := pointsContraction I A B
    ∃ d : DecidableRel Q,
      (∀ l, @pts _ _ _ Q d l=3) ∧ (∀ v, @lns _ _ _ Q d v=3) ∧
      (∀ (l : In A) (x y : V), B x=false → B y=false → I l.val x → I l.val y → x=y) := by
  classical
  dsimp only
  let A (l : L) : Bool := decide (l∈S)
  let B (v : V) : Bool := decide (v∈T)
  let Q := pointsContraction I A B
  let d : DecidableRel Q := fun _ _ => Classical.propDecidable _
  let D : DecidableRel (fun v l => Q l v) := fun v l => d l v
  letI := d
  letI := D
  have H : NoSmallCut Q := minimal_contraction_no_cut I S T large inward tight mini
  have ⟨rsize,csize⟩ := contraction_size I S T large inward tight col M
  obtain ⟨m,hm⟩ := M
  obtain ⟨q,hq,_⟩ := project_original I A B inward tight m hm
  have Mt : ∃ f : In A ≃ Option (In B), ∀ l, Q l (f l) :=
    ⟨q.symm,fun l => by simpa using hq (q.symm l)⟩
  have rlower (l : In A) : 3≤pts Q l :=
    no_small_cut_degree (fun v l => Q l v) (no_small_cut_transpose Q H) Mt rsize l
  have r (l : In A) : pts Q l=3 := by
    apply Nat.le_antisymm _ (rlower l)
    unfold pts at *
    rw [contraction_neighbors I A B l]
    exact card_image_le.trans (le_of_eq (row l.val))
  have clower (v : Option (In B)) : 3≤lns Q v := no_small_cut_degree Q H ⟨q,hq⟩ csize v
  have equal := counts Q
  rw [show (∑ l : In A, pts Q l)=(∑ v : Option (In B), (3 : Nat)) by
    simp only [r,sum_const,card_univ,nsmul_eq_mul,Fintype.card_congr q]] at equal
  have c (v : Option (In B)) : lns Q v=3 :=
    le_antisymm (le_of_not_gt (fun gt => (Nat.lt_irrefl _) ((sum_lt_sum (fun i _ => clower i)
      ⟨v,mem_univ _,gt⟩).trans_le (le_of_eq equal.symm)))) (clower v)
  refine ⟨d,r,c,?_⟩
  intro l x y xo yo ix iy
  let N : Finset V := univ.filter fun v => I l.val v
  have ec : (N.image (portMap B)).card=N.card := by
    have z := r l
    unfold pts at z
    rw [contraction_neighbors I A B l] at z
    exact z.trans (row l.val).symm
  have inj := Finset.injOn_of_card_image_eq ec
  exact inj (mem_filter.mpr ⟨mem_univ _,ix⟩) (mem_filter.mpr ⟨mem_univ _,iy⟩) (by change B x=false at xo; change B y=false at yo; simp [portMap,xo,yo])

#print axioms cubic_contraction
end FolkmanB4.Tight
